#!/usr/bin/env python3

import argparse
import copy
import json
from threading import Lock
import requests
import os
import sqlite3
import sys
from graphviz import Digraph
import datetime
import re
import toml
from flask import Flask, request, abort, send_from_directory
import time

# sortition_db = "mainnet/burnchain/sortition/marf.sqlite"
# chainstate_db = "mainnet/chainstate/vm/index.sqlite"
# mempool_db = "mainnet/chainstate/mempool.sqlite"
sortition_db = "nakamoto-neon/burnchain/sortition/marf.sqlite"
chainstate_db = "nakamoto-neon/chainstate/vm/index.sqlite"
mempool_db = "nakamoto-neon/chainstate/mempool.sqlite"
default_color = "white"
cost_limits = {
    "write_length": 15_000_000,
    "write_count": 15_000,
    "read_length": 100_000_000,
    "read_count": 15_000,
    "runtime": 5_000_000_000,
    "size": 2 * 1024 * 1024,
}
bitcoin_tx_db = "output/bitcoin-tx.sqlite"
bitcoin_api_url = "https://mempool.space/api/tx"


def is_miner_known(miner_config, identifier):
    # Check if the miner is in the config
    return identifier in miner_config.get("miners", {})


def is_miner_tracked(miner_config, identifier):
    # Check if the miner is in tracked group
    tracked_group = miner_config.get("tracked_group", None)
    if not tracked_group:
        return False

    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info and miner_info.get("group", None) == tracked_group:
        return True
    return False


def get_miner_color(miner_config, identifier):
    # Retrieve the color for the given miner identifier
    miner_info = miner_config.get("miners", {}).get(identifier)
    if not miner_info or not miner_info.get("group", None):
        return default_color

    group = miner_config.get("groups", {}).get(miner_info.get("group"), None)
    if not group:
        return default_color

    return group.get("color", default_color)


def get_miner_name(miner_config, identifier):
    # Retrieve the name for the given miner identifier
    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info:
        return miner_info.get("name", identifier[0:8])
    return identifier[0:8]


def get_miner_group(miner_config, identifier):
    # Retrieve the name for the given miner identifier
    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info:
        return miner_info.get("group", "Other")
    return "Other"


class Commit:
    def __init__(
        self,
        burn_header_hash,
        txid,
        sender,
        burn_block_height,
        spend,
        sortition_id,
        parent=None,
        stacks_height=None,
        block_hash=None,
        won=False,
        canonical=False,
        tip=False,
        coinbase_earned=0,
        fees_earned=0,
        read_length=0,
        read_count=0,
        write_length=0,
        write_count=0,
        runtime=0,
        block_size=0,
        potential_tip=False,
        next_tip=False,
    ):
        self.burn_header_hash = burn_header_hash
        self.txid = txid
        self.sender = sender[1:-1]  # Remove quotes
        self.burn_block_height = burn_block_height
        self.spend = spend
        self.sortition_id = sortition_id
        self.parent = parent
        self.stacks_height = stacks_height
        self.block_hash = block_hash
        self.won = won
        self.canonical = canonical
        self.tip = tip
        self.coinbase_earned = coinbase_earned
        self.fees_earned = fees_earned
        self.read_length = read_length
        self.read_count = read_count
        self.write_length = write_length
        self.write_count = write_count
        self.runtime = runtime
        self.block_size = block_size
        self.potential_tip = potential_tip
        self.next_tip = next_tip

    def __repr__(self):
        return f"Commit({self.burn_header_hash[:8]}, Burn Block Height: {self.burn_block_height}, Spend: {self.spend:,})"

    def get_fullness(self):
        fullness = max(
            self.read_length / cost_limits["read_length"],
            self.read_count / cost_limits["read_count"],
            self.write_length / cost_limits["write_length"],
            self.write_count / cost_limits["write_count"],
            self.runtime / cost_limits["runtime"],
            self.block_size / cost_limits["size"],
        )
        return round(fullness * 100, 2)


class Miner:
    def __init__(self, address, name, group, color, tracked, known):
        self.address = address
        self.name = name
        self.group = group
        self.color = color
        self.tracked = tracked
        self.known = known

    def __repr__(self):
        return f"Miner({self.address}, {self.name}, {self.group})"


def get_block_commits_with_parents(db_path, start_block, start_height_30, num_blocks=100):
    conn = sqlite3.connect(os.path.join(db_path, sortition_db))
    cursor = conn.cursor()

    lower_bound_height = start_block - num_blocks

    # Fetch the necessary data to build the graph
    query = """
    SELECT
        block_header_hash,
        burn_header_hash,
        txid,
        apparent_sender,
        sortition_id,
        vtxindex,
        block_height,
        burn_fee,
        parent_block_ptr,
        parent_vtxindex
    FROM
        block_commits
    WHERE
        block_height BETWEEN ? AND ?
    ORDER BY
        block_height ASC
    """
    cursor.execute(query, (lower_bound_height, start_block))
    raw_commits = cursor.fetchall()

    # Prepare dictionaries to hold the parent hashes and total spends
    parent_hashes = {}
    sortition_sats = {}
    commits = {}  # Track all nodes, by header_hash

    for (
        block_header_hash,
        burn_header_hash,
        txid,
        apparent_sender,
        sortition_id,
        vtxindex,
        block_height,
        burn_fee,
        parent_block_ptr,
        parent_vtxindex,
    ) in raw_commits:
        if block_height >= start_height_30:
            parent = parent_hashes.get((parent_block_ptr, parent_vtxindex))

            commits[burn_header_hash] = Commit(
                burn_header_hash,
                txid,
                apparent_sender,
                block_height,
                int(burn_fee),
                sortition_id,
                parent,
            )
            parent_hashes[(block_height, vtxindex)] = burn_header_hash
            sortition_sats[sortition_id] = sortition_sats.get(sortition_id, 0) + int(
                burn_fee
            )
        else:
            parent = parent_hashes.get((parent_block_ptr, parent_vtxindex))

            commits[block_header_hash] = Commit(
                block_header_hash,
                txid,
                apparent_sender,
                block_height,
                int(burn_fee),
                sortition_id,
                parent,
            )
            parent_hashes[(block_height, vtxindex)] = block_header_hash
            sortition_sats[sortition_id] = sortition_sats.get(sortition_id, 0) + int(
                burn_fee
            )

    conn.close()
    return commits, sortition_sats


def mark_canonical_blocks(db_path, commits, start_block, start_height_30):
    conn = sqlite3.connect(os.path.join(db_path, sortition_db))
    cursor = conn.cursor()

    for block_height in sorted(
        set(commit.burn_block_height for commit in commits.values())
    ):
        if block_height >= start_height_30:
            (winning_block_txid, stacks_height, consensus_hash) = cursor.execute(
                "SELECT winning_block_txid, canonical_stacks_tip_height, consensus_hash FROM snapshots WHERE block_height = ?;",
                (block_height,),
            ).fetchone()
            stacks_height = stacks_height + 1
        else:
            (winning_block_txid, stacks_height, consensus_hash) = cursor.execute(
                "SELECT winning_block_txid, stacks_block_height, consensus_hash FROM snapshots WHERE block_height = ?;",
                (block_height,),
            ).fetchone()

        for commit in filter(
            lambda x: x.burn_block_height == block_height, commits.values()
        ):
            # If the stacks_height is 0, this block has not been processed yet.
            if winning_block_txid == commit.txid:
                commit.won = True
                commit.potential_tip = True
                commit.stacks_height = stacks_height

                # The parent of this node is no longer a potential tip
                if commit.parent and commit.parent in commits:
                    parent_commit = commits[commit.parent]
                    parent_commit.potential_tip = False
                    commit.stacks_height = stacks_height

                # If the stacks_height is greater than 0, this block has been processed.
                if stacks_height > 0:
                    # Fetch the coinbase and fees earned
                    chainstate_conn = sqlite3.connect(
                        os.path.join(db_path, chainstate_db)
                    )
                    chainstate_cursor = chainstate_conn.cursor()
                    # Execute the query
                    if block_height >= start_height_30:
                        result = chainstate_cursor.execute(
                            "SELECT block_hash, coinbase FROM payments WHERE consensus_hash = ?;",
                            (consensus_hash,),
                        ).fetchone()

                        max_fees = chainstate_cursor.execute(
                            "SELECT tenure_tx_fees FROM nakamoto_block_headers WHERE burn_header_height = ? ORDER BY height_in_tenure DESC LIMIT 1;",
                            (block_height,),
                        ).fetchone()

                        if result and max_fees:
                            (
                                block_hash,
                                coinbase,
                            ) = result
                            (
                                fees,
                            ) = max_fees
                            commit.block_hash = block_hash
                            commit.coinbase_earned = int(coinbase)
                            commit.fees_earned = int(fees)

                        # Fetch the block costs and size
                        result = chainstate_cursor.execute(
                            "SELECT cost, block_size FROM nakamoto_block_headers WHERE block_hash = ?;",
                            (block_hash,),
                        ).fetchone()
                        if result:
                            cost_string, block_size = result
                            costs = json.loads(cost_string)
                            commit.read_length = int(costs["read_length"])
                            commit.read_count = int(costs["read_count"])
                            commit.write_length = int(costs["write_length"])
                            commit.write_count = int(costs["write_count"])
                            commit.runtime = int(costs["runtime"])
                            commit.block_size = int(block_size)
                    else:
                        result = chainstate_cursor.execute(
                            "SELECT block_hash, coinbase, tx_fees_anchored, tx_fees_streamed FROM payments WHERE consensus_hash = ?;",
                            (consensus_hash,),
                        ).fetchone()

                        if result:
                            (
                                block_hash,
                                coinbase,
                                tx_fees_anchored,
                                tx_fees_streamed,
                            ) = result
                            commit.block_hash = block_hash
                            commit.coinbase_earned = int(coinbase)
                            commit.fees_earned = int(tx_fees_anchored) + int(
                                tx_fees_streamed
                            )

                        # Fetch the block costs and size
                        result = chainstate_cursor.execute(
                            "SELECT cost, block_size FROM block_headers WHERE block_hash = ?;",
                            (block_hash,),
                        ).fetchone()
                        if result:
                            cost_string, block_size = result
                            costs = json.loads(cost_string)
                            commit.read_length = int(costs["read_length"])
                            commit.read_count = int(costs["read_count"])
                            commit.write_length = int(costs["write_length"])
                            commit.write_count = int(costs["write_count"])
                            commit.runtime = int(costs["runtime"])
                            commit.block_size = int(block_size)

                    chainstate_conn.close()

            else:
                if commit.parent and commit.parent in commits:
                    parent_commit = commits[commit.parent]
                    commit.stacks_height = parent_commit.stacks_height + 1

    # Mark the canonical chain
    if block_height >= start_height_30:
        canonical_tip = cursor.execute(
            "SELECT burn_header_hash FROM snapshots WHERE block_height = ?;",
            (start_block,),
        ).fetchone()[0]
    else:
        canonical_tip = cursor.execute(
            "SELECT canonical_stacks_tip_hash FROM snapshots WHERE block_height = ?;",
            (start_block,),
        ).fetchone()[0]
    conn.close()
    if canonical_tip in commits:
        commits[canonical_tip].tip = True
        tip = canonical_tip
        while tip and tip in commits:
            commits[tip].canonical = True
            tip = commits[tip].parent

    return canonical_tip


def create_graph(miner_config, commits, sortition_sats):
    dot = Digraph(comment="Mining Status")

    # Keep track of a representative node for each cluster to enforce order
    last_height = None

    # Group nodes by block_height and create edges to parent nodes
    for block_height in sorted(
        set(commit.burn_block_height for commit in commits.values())
    ):
        tracked_spend = 0
        with dot.subgraph(name=f"cluster_{block_height}") as c:
            for commit in filter(
                lambda x: x.burn_block_height == block_height, commits.values()
            ):
                node_label = f"""{get_miner_name(miner_config, commit.sender)}
{round(commit.spend/1000.0):,}K ({commit.spend/sortition_sats[commit.sortition_id]:.0%})
Height: {commit.stacks_height}"""
                if commit.won:
                    node_label += f"\n{commit.get_fullness()}% full"

                if miner_config.get("track_all", False) or is_miner_tracked(
                    miner_config, commit.sender
                ):
                    tracked_spend += commit.spend

                c.attr(
                    label=f"""Burn Block Height: {commit.burn_block_height}
Total Spend: {sortition_sats[commit.sortition_id]:,}
Tracked Spend: {tracked_spend:,} ({tracked_spend/sortition_sats[commit.sortition_id]:.2%})"""
                )

                # Initialize the node attributes dictionary
                node_attrs = {
                    "color": (
                        "#00FF00"
                        if commit.next_tip
                        else "blue" if commit.won else "black"
                    ),
                    "fillcolor": get_miner_color(miner_config, commit.sender),
                    "penwidth": "8" if commit.tip else "4" if commit.won else "1",
                    "style": "filled,solid",
                }

                # Additional modifications based on conditions
                if not commit.canonical:
                    node_attrs["style"] = "filled,dashed"

                # Check if the commit spent more than the highlight_sats threshold
                if commit.spend >= miner_config.get("highlight_sats", 1000000):
                    node_attrs["fontcolor"] = "red"
                    node_attrs["fontname"] = "bold"

                # If we have the block hash, link to the explorer
                if commit.block_hash:
                    node_attrs["href"] = (
                        f"https://explorer.hiro.so/block/0x{commit.block_hash}"
                    )

                # Now use the dictionary to set attributes
                c.node(commit.burn_header_hash, node_label, **node_attrs)

                if commit.parent:
                    # If the parent is not the previous block, color the edge red
                    color = "black"
                    penwidth = "1"
                    if commits[commit.parent].burn_block_height != last_height:
                        color = "red"
                        penwidth = "4"
                    if commit.canonical:
                        color = "blue"
                        penwidth = "8"
                    c.edge(
                        commit.parent,
                        commit.burn_header_hash,
                        color=color,
                        penwidth=penwidth,
                    )

            last_height = block_height

    return dot.pipe(format="svg").decode("utf-8")


# Using the RPC endpoints from the node won't work because this endpoint does
# not explicitly return the fee. It can be looked up from the data returned
# here, but that would require retrieving the input UTXO and calculating the
# fee manually. Since we don't have the block hash for the input UTXO, and
# the node doesn't have transaction indexing enabled (txindex=1), we can't
# look up the input UTXO.
def get_bitcoin_transaction_rpc(bitcoin_rpc_url, txid, block_hash):
    payload = {
        "method": "getrawtransaction",
        "params": [txid, True, block_hash],
        "jsonrpc": "2.0",
        "id": 1,
    }
    headers = {"content-type": "application/json"}
    response = requests.post(bitcoin_rpc_url, data=json.dumps(payload), headers=headers)
    return response.json()


def ensure_bitcoin_tx_db_exists():
    # Create the bitcoin transaction database's folder if it doesn't exist
    bitcoin_db_folder = os.path.dirname(os.path.abspath(bitcoin_tx_db))
    os.makedirs(bitcoin_db_folder, exist_ok=True)

    # Connect to the SQLite database (this will create it if it doesn't exist)
    conn = sqlite3.connect(bitcoin_tx_db)

    # Create the table if it doesn't exist
    conn.execute(
        """CREATE TABLE IF NOT EXISTS bitcoin_transactions
                 (txid TEXT PRIMARY KEY, 
                  fee INTEGER)"""
    )
    conn.commit()
    conn.close()


def get_bitcoin_fee(txid):
    # Connect to the database
    conn = sqlite3.connect(bitcoin_tx_db)
    cursor = conn.cursor()

    # Try to fetch the transaction from the database
    cursor.execute("SELECT fee FROM bitcoin_transactions WHERE txid = ?", (txid,))
    row = cursor.fetchone()

    if row:
        # If found in the database, return the data
        conn.close()
        return row[0]
    else:
        # If not found, fetch from the API
        url = f"{bitcoin_api_url}/{txid}"
        response = requests.get(url)

        if response.status_code == 200:
            # Store the fetched data in the database
            cursor.execute(
                "INSERT INTO bitcoin_transactions (txid, fee) VALUES (?, ?)",
                (txid, response.json()["fee"]),
            )
            conn.commit()
            conn.close()
            return response.json()["fee"]
        elif response.status_code == 429:
            conn.close()
            time.sleep(1)
            return get_bitcoin_fee(txid)
        else:
            conn.close()
            return None


zero_stats = {
    "commits": 0,
    "wins": 0,
    "canonical": 0,
    "spend": 0,
    "btc_fees": 0,
    "coinbase_earned": 0,
    "fees_earned": 0,
    "spend_by_block": {},
}


def compute_stats(stats, num_blocks):
    total_earned = stats["coinbase_earned"] + stats["fees_earned"]
    return {
        "spend": stats["spend"],
        "btc_fees": stats["btc_fees"],
        "total_spend": stats["spend"] + stats["btc_fees"],
        "spend_by_block": stats["spend_by_block"],
        "coinbase_earned": stats["coinbase_earned"],
        "fees_earned": stats["fees_earned"],
        "avg_spend_per_block": round(stats["spend"] / num_blocks),
        "win_percentage": stats["wins"] / num_blocks,
        "canonical_percentage": stats["canonical"] / num_blocks,
        "orphan_rate": (
            (stats["wins"] - stats["canonical"]) / stats["wins"]
            if stats["wins"] > 0
            else 0
        ),
        "price_ratio": (
            f"{(stats['spend'] + stats['btc_fees']) / (total_earned / 1000000.0):.2f}"
            if total_earned > 0
            else "0" if stats["spend"] == 0 else "∞"
        ),
        "total_earned": total_earned,
    }


def collect_stats(miner_config, commits):
    group_stats = {}
    blocks = set()
    orphans = 0
    total_blocks = 0
    miners = {}
    spend_by_block = {}
    earn_by_block = {}
    for commit in commits.values():
        # Track the blocks
        blocks.add(commit.burn_block_height)

        # Track the stats per group
        group = get_miner_group(miner_config, commit.sender)
        stats = group_stats.get(group, copy.deepcopy(zero_stats))

        stats["commits"] += 1
        stats["spend"] += commit.spend

        fee = get_bitcoin_fee(commit.txid)
        if not fee:
            fee = 0
        stats["btc_fees"] += fee

        # Track the total spend for each block
        spend_by_block[commit.burn_block_height] = (
            spend_by_block.get(commit.burn_block_height, 0) + commit.spend + fee
        )

        # Track the total spend by the group for each block
        stats["spend_by_block"][commit.burn_block_height] = (
            stats["spend_by_block"].get(commit.burn_block_height, 0)
            + commit.spend
            + fee
        )

        # Track the total coinbase and fees earned for each block
        earn_by_block[commit.burn_block_height] = (
            earn_by_block.get(commit.burn_block_height, 0)
            + commit.coinbase_earned
            + commit.fees_earned
        )

        if commit.won:
            # Track the overall orphan rate
            total_blocks += 1
            if not commit.canonical:
                orphans += 1

            stats["wins"] += 1

            if commit.canonical:
                stats["canonical"] += 1

                stats["coinbase_earned"] += commit.coinbase_earned
                stats["fees_earned"] += commit.fees_earned

        # Keep track of all miners
        if commit.sender not in miners:
            miners[commit.sender] = Miner(
                commit.sender,
                get_miner_name(miner_config, commit.sender),
                group,
                get_miner_color(miner_config, commit.sender),
                is_miner_tracked(miner_config, commit.sender),
                is_miner_known(miner_config, commit.sender),
            )

        group_stats[group] = stats

    computed_stats = {
        key: compute_stats(value, len(blocks)) for key, value in group_stats.items()
    }

    # Load the STX price (in Sats) from the file
    price_path = "stx-price.txt"
    with open(price_path, "r") as file:
        stx_price = float(file.read())

    return {
        "group_stats": computed_stats,
        "miners": miners,
        "spend_by_block": spend_by_block,
        "earn_by_block": earn_by_block,
        "orphan_rate": orphans / total_blocks if total_blocks > 0 else 0,
        "stx_price": stx_price,
    }


def generate_html(n_blocks, svg_content, stats):
    current_time = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # Use regex to replace width and height attributes in the SVG
    svg_content = re.sub(r'width="\d+pt"', 'width="100%"', svg_content)
    svg_content = re.sub(r'height="\d+pt"', 'height="100%"', svg_content)

    group_stats = stats["group_stats"]

    # Build the stats table
    table_str = "<table>"

    # Header row with group names
    table_str += "<tr><th>Stat Name</th>"
    for group_name in group_stats.keys():
        table_str += f"<th>{group_name}</th>"
    table_str += "</tr>"

    # Rows for each stat
    stat_names = [
        ("spend", "Total PoX spend"),
        ("btc_fees", "Total Bitcoin fees"),
        ("total_spend", "Total spend"),
        ("coinbase_earned", "Total coinbase earned"),
        ("fees_earned", "Total fees earned"),
        ("total_earned", "Total earned"),
        ("avg_spend_per_block", "Avg spend per block"),
        ("win_percentage", "Win %"),
        ("canonical_percentage", "Canonical %"),
        ("price_ratio", "Price ratio"),
        ("orphan_rate", "Orphan rate"),
    ]
    for stat_name, stat_label in stat_names:
        table_str += f"<tr><th>{stat_label}</th>"
        for group in group_stats.values():
            if stat_name == "price_ratio":
                value = f"{group[stat_name]} Sats/STX"
            elif stat_name in ["win_percentage", "canonical_percentage", "orphan_rate"]:
                value = f"{group[stat_name]:.2%}"
            elif stat_name in ["coinbase_earned", "fees_earned", "total_earned"]:
                value = f"{(group[stat_name] / 1000000.0):,} STX"
            elif stat_name in [
                "spend",
                "avg_spend_per_block",
                "btc_fees",
                "total_spend",
            ]:
                value = f"{group[stat_name]:,} Sats"
            else:
                value = f"{group[stat_name]:,}"
            table_str += f"<td>{value}</td>"
        table_str += "</tr>"

    # End of the table
    table_str += "</table>"

    miner_rows = "".join(
        f"""
            <tr>
                <td>{miner.name}</td>
                <td>{miner.address}</td>
                <td>{miner.group}</td>
                <td><span class="color-sample" style="background-color: {miner.color};"></span>{miner.color}</td>
                <td class="center-text">{"✅" if miner.tracked else ""}</td>
            </tr>
            """
        for miner in stats["miners"].values()
    )

    html_content = f"""
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <title>Block Commits Visualization</title>
        <style>
            .responsive-svg {{
                max-width: 100%;
                height: auto;
            }}
            table, th, td {{
                border: 1px solid black;
                border-collapse: collapse;
            }}
            th, td {{
                padding: 5px;
                text-align: left;
            }}
            .color-sample {{
                width: 20px;
                height: 20px;
                border-radius: 50%;
                border: 2px solid black;
                display: inline-block;
                margin-right: 5px;
            }}
            .center-text {{
                text-align: center;
            }}
        </style>
    </head>
    <body>
        <nav>
            <ul style="list-style-type: none; padding: 0;">
                <li style="display: inline; margin-right: 20px;"><a href="/">Home</a></li>
                <li style="display: inline; margin-right: 20px;"><a href="/50.html">50 Blocks</a></li>
                <li style="display: inline;"><a href="/100.html">100 Blocks</a></li>
            </ul>
        </nav>
        <p>This page was last updated at: {current_time}<br>Note: Data refreshes every minute. Refresh the page for the latest.</p>
        <h1>Last {n_blocks} Blocks</h1>
        <h2>Network Stats</h2>
        <ul>
            <!-- <li><b>Ready transactions:</b> {stats['mempool']['ready_tx_count']}</li>
            <li><b>Pending transactions:</b> {stats['mempool']['pending_tx_count']}</li> -->
            <li><b>Network orphan rate:</b> {stats['orphan_rate']:.2%}</li>
            <li><b>STX Price:</b> {stats['stx_price']:.2f} Sats</li>
        </ul>
        <h2>Miner Stats</h2>
        {table_str}
        <h2>Block Commits</h2>
        <div class="responsive-svg">
            {svg_content}
        </div>
        <h2>Legend</h2>
        <table>
            <tr>
                <th>Name</th>
                <th>Address</th>
                <th>Group</th>
                <th>Color</th>
                <th>Tracked?</th>
            </tr>
            {miner_rows}
        </table>
    </body>
    </html>
    """
    return html_content


def send_new_miner_alerts(miner_config, stats):
    webhook = miner_config.get("alert_webhook")
    if not webhook:
        return

    # Send an alert if there are any new miners
    new_miners = list(filter(lambda x: not x.known, stats["miners"].values()))
    if len(new_miners) == 0:
        return

    data_to_send = {
        "type": "new_miners",
        "block_height": max(stats["spend_by_block"].keys()),
        "new_miners": list(map(lambda x: x.address, new_miners)),
    }
    json_data = json.dumps(data_to_send)

    response = requests.post(
        webhook, data=json_data, headers={"Content-Type": "application/json"}
    )

    # Check if the POST request was successful
    if response.status_code != 200:
        print(
            f"Failed to send miner alert. Status code: {response.status_code}, Response: {response.text}"
        )

    # Update the config file with the new miners, so that we don't send alerts again
    for miner in new_miners:
        miner_config["miners"][miner.address] = {
            "name": miner.name,
            "group": miner.group,
        }
    with open(args.config_path, "w") as file:
        toml.dump(miner_config, file)


def send_high_spend_alerts(miner_config, stats):
    webhook = miner_config.get("alert_webhook")
    alert_group_spend_sats = miner_config.get("alert_group_spend_sats")
    if not webhook or not alert_group_spend_sats:
        return

    start_block = miner_config.get("last_alert_block_high", 0)
    for group, group_stats in stats.get("group_stats").items():
        for block_height, spend in group_stats.get("spend_by_block").items():
            if block_height <= start_block:
                continue

            if spend > alert_group_spend_sats:
                data_to_send = {
                    "type": "high_spend",
                    "group": group,
                    "block_height": block_height,
                    "spend": spend,
                }
                json_data = json.dumps(data_to_send)

                print(
                    f"High spend detected for block {block_height}: group {group} spent {spend:,} Sats"
                )
                response = requests.post(
                    webhook,
                    data=json_data,
                    headers={"Content-Type": "application/json"},
                )

                # Check if the POST request was successful
                if response.status_code != 200:
                    print(
                        f"Failed to send spend alert. Status code: {response.status_code}, Response: {response.text}"
                    )

            # Update the config file with the last alert block to avoid repeat alerts
            miner_config["last_alert_block_high"] = block_height
            with open(args.config_path, "w") as file:
                toml.dump(miner_config, file)


def send_low_spend_alerts(miner_config, stats):
    webhook = miner_config.get("alert_webhook")
    alert_low_total_spend = miner_config.get("alert_low_total_spend")
    if not webhook or not alert_low_total_spend:
        return

    last_alert_block = miner_config.get("last_alert_block_low", 0)

    blocks = stats["spend_by_block"].keys()
    last5 = sorted(blocks, reverse=True)[:5]

    # Check if we've already alerted on this block
    if last5[0] <= last_alert_block:
        return

    # Compute the average price (Sats/STX) for the last 5 blocks
    last5_spend = sum(stats["spend_by_block"][block] for block in last5)
    last5_earned = sum(stats["earn_by_block"][block] for block in last5)
    last5_price_ratio = (
        last5_spend / (last5_earned / 1000000.0) if last5_earned != 0 else 0
    )

    # Send an alert if the price ratio is below the threshold
    if last5_price_ratio < (stats["stx_price"] * alert_low_total_spend):
        data_to_send = {
            "type": "low_spend",
            "block_height": last5[0],
            "last5_price": round(last5_price_ratio),
            "market_price": round(stats["stx_price"]),
        }
        json_data = json.dumps(data_to_send)

        print(
            f"Low spend detected: {last5_price_ratio:.2f} Sats/STX (threshold: {stats['stx_price'] * alert_low_total_spend:.2f} Sats/STX)"
        )

        response = requests.post(
            webhook, data=json_data, headers={"Content-Type": "application/json"}
        )

        # Check if the POST request was successful
        if response.status_code != 200:
            print(
                f"Failed to send low spend alert. Status code: {response.status_code}, Response: {response.text}"
            )

    # Update the config file with the last alert block to avoid repeat alerts
    miner_config["last_alert_block_low"] = last5[0]
    with open(args.config_path, "w") as file:
        toml.dump(miner_config, file)


def send_no_canonical_block_alert(miner_config):
    webhook = miner_config.get("alert_webhook")
    alert_low_total_spend = miner_config.get("alert_low_total_spend")
    if not webhook or not alert_low_total_spend:
        return

    tip = get_tip(miner_config.get("node").get("working_dir"))

    last_alert_block = miner_config.get("last_block", tip)
    last_alert_time = miner_config.get("last_alert_time", int(time.time()))

    if tip == last_alert_block:
        return

    if time.time() - last_alert_time < 3600:
        return

    data_to_send = {
        "type": "no_canonical_block",
        "block_height": tip,
    }
    json_data = json.dumps(data_to_send)

    print(f"No canonical block detected: {tip}")

    response = requests.post(
        webhook, data=json_data, headers={"Content-Type": "application/json"}
    )

    # Check if the POST request was successful
    if response.status_code != 200:
        print(
            f"Failed to send no canonical block alert. Status code: {response.status_code}, Response: {response.text}"
        )

    # Update the config file with the last alert block to avoid repeat alerts
    miner_config["last_block"] = tip
    miner_config["last_alert_time"] = int(time.time())
    with open(args.config_path, "w") as file:
        toml.dump(miner_config, file)


def get_mempool_stats(db_path):
    ready_query = """SELECT COUNT(*)
FROM mempool m
INNER JOIN nonces n_origin ON m.origin_address = n_origin.address
LEFT JOIN nonces n_sponsor ON m.sponsor_address = n_sponsor.address AND m.sponsor_address != ''
WHERE m.origin_nonce = (n_origin.nonce + 1)
  AND (m.sponsor_address = '' OR m.sponsor_nonce = (n_sponsor.nonce + 1));"""
    pending_query = """SELECT COUNT(*)
FROM mempool m
INNER JOIN nonces n_origin ON m.origin_address = n_origin.address
LEFT JOIN nonces n_sponsor ON m.sponsor_address = n_sponsor.address AND m.sponsor_address != ''
WHERE m.origin_nonce > (n_origin.nonce + 1)
  AND (m.sponsor_address = '' OR m.sponsor_nonce > (n_sponsor.nonce + 1));"""
    old_query = """SELECT COUNT(*)
FROM mempool m
INNER JOIN nonces n_origin ON m.origin_address = n_origin.address
LEFT JOIN nonces n_sponsor ON m.sponsor_address = n_sponsor.address AND m.sponsor_address != ''
WHERE m.origin_nonce <= (n_origin.nonce + 1)
  AND (m.sponsor_address = '' OR m.sponsor_nonce <= (n_sponsor.nonce + 1));"""

    conn = sqlite3.connect(os.path.join(db_path, mempool_db))
    cursor = conn.cursor()
    ready_tx_count = cursor.execute(ready_query).fetchone()[0]
    pending_tx_count = cursor.execute(pending_query).fetchone()[0]
    old_tx_count = cursor.execute(old_query).fetchone()[0]
    conn.close()

    return {
        "ready_tx_count": ready_tx_count,
        "pending_tx_count": pending_tx_count,
        "old_tx_count": old_tx_count,
    }


def get_score_to_common_ancestor(tips, commits):
    if not tips:
        return None

    scores = {}

    # Bring all tips to the same stacks_height
    min_height = min(commit.stacks_height for commit in tips)
    max_height = max(commit.stacks_height for commit in tips)

    tips_at_same_height = []
    for tip in tips:
        scores[tip.burn_header_hash] = (
            commits[tip.burn_header_hash].burn_block_height
            - commits[tip.burn_header_hash].stacks_height
        ) * (max_height - commits[tip.burn_header_hash].stacks_height)
        commit = tip
        while commit.stacks_height > min_height:
            scores[tip.burn_header_hash] += (
                commit.burn_block_height - commit.stacks_height
            )
            commit = commits.get(commit.parent)
        tips_at_same_height.append((tip, commit))

    # Trace back ancestors until a common ancestor is found
    while any(
        commit != tips_at_same_height[0][1] for tip, commit in tips_at_same_height
    ):
        tips_at_same_height = [
            (tip, commits.get(commit.parent)) if commit else None
            for tip, commit in tips_at_same_height
        ]

        # If any commit becomes None (reaches the beginning), there is no common ancestor
        if any(commit is None for tip, commit in tips_at_same_height):
            return None

        # Update the scores
        for tip, commit in tips_at_same_height:
            scores[tip.burn_header_hash] += (
                commit.burn_block_height - commit.stacks_height
            )

    return scores


def mark_next_tip(canonical_tip, max_fork_depth, commits):
    tips = []
    min_height = commits[canonical_tip].stacks_height - max_fork_depth
    for commit in commits.values():
        if commit.potential_tip and commit.stacks_height >= min_height:
            tips.append(commit)

    scores = get_score_to_common_ancestor(tips, commits)
    if scores:
        next_tip = min(scores, key=scores.get)
        commits[next_tip].next_tip = True


def run_server(args):
    app = Flask(__name__, static_folder="output", static_url_path="")
    lock = Lock()

    @app.route("/new_block", methods=["POST"])
    def new_block():
        # Check if the request is from localhost
        if request.remote_addr != "127.0.0.1":
            abort(403)  # Forbidden access

        print("Received new block notification")

        # Acquire the lock before running the command line operation
        if lock.acquire(blocking=False):
            try:
                run_command_line(args)
                print("Graphs rebuilt")
            finally:
                lock.release()  # Ensure the lock is released
            return "Graphs rebuilt", 200
        else:
            return "Another operation is currently in progress", 429

    @app.route("/")
    def index():
        return app.send_static_file("index.html")

    @app.route("/<path:path>")
    def static_file(path):
        return send_from_directory(app.static_folder, path)

    app.run(host="0.0.0.0", port=8080)


def get_tip(db_path):
    conn = sqlite3.connect(os.path.join(db_path, sortition_db))
    cursor = conn.cursor()

    # Pre-compute the maximum block height
    cursor.execute("SELECT MAX(block_height) FROM block_commits")
    tip = cursor.fetchone()[0]
    conn.close()
    return tip


def get_epoch_30_start_block(db_path):
    conn = sqlite3.connect(os.path.join(db_path, sortition_db))
    cursor = conn.cursor()

    result = cursor.execute(
        "SELECT start_block_height FROM epochs WHERE epoch_id = 12288",
        (),
    ).fetchone()

    conn.close()

    if result:
        (
            start_block_height,
        ) = result
        return start_block_height
    else:
        return 0


def run_command_line(args):
    with open(args.config_path, "r") as file:
        miner_config = toml.load(file)

    if args.at_tip:
        start_block = int(args.at_tip)
    else:
        start_block = get_tip(miner_config.get("node").get("working_dir"))

    ensure_bitcoin_tx_db_exists()

    start_height_30 = get_epoch_30_start_block(miner_config.get("node").get("working_dir"))

    for index, num_blocks in enumerate(args.block_counts):
        print(f"Generating graph for blocks...")
        commits, sortition_sats = get_block_commits_with_parents(
            miner_config.get("node").get("working_dir"), start_block, start_height_30, num_blocks
        )
        canonical_tip = mark_canonical_blocks(
            miner_config.get("node").get("working_dir"), commits, start_block, start_height_30
        )
        mark_next_tip(canonical_tip, miner_config.get("max_fork_depth", 3), commits)

        svg_string = create_graph(miner_config, commits, sortition_sats)

        stats = collect_stats(miner_config, commits)
        stats["mempool"] = get_mempool_stats(miner_config.get("node").get("working_dir"))

        send_new_miner_alerts(miner_config, stats)
        send_high_spend_alerts(miner_config, stats)
        send_low_spend_alerts(miner_config, stats)

        if args.print_stats:
            # print(f"Ready transactions: {stats['mempool']['ready_tx_count']}")
            # print(f"Pending transactions: {stats['mempool']['pending_tx_count']}")
            print(f"Network orphan rate: {stats['orphan_rate']:.2%}")
            print(f"STX Price: {stats['stx_price']:.2f} Sats")
            for group, group_stats in stats["group_stats"].items():
                print(f"Group: {group}")
                print(f"  PoX spend: {group_stats['spend']:,} Sats")
                print(f"  Bitcoin fees: {group_stats['btc_fees']:,} Sats")
                print(f"  Total spend: {group_stats['btc_fees']:,} Sats")
                print(
                    f"  Total coinbase earned: {(group_stats['coinbase_earned']/1000000.0):,} STX"
                )
                print(
                    f"  Total fees earned: {(group_stats['fees_earned']/1000000.0):,} STX"
                )
                print(
                    f"  Total earned: {((group_stats['coinbase_earned'] + group_stats['fees_earned'])/1000000.0):,} STX"
                )
                print(
                    f"  Avg spend per block: {group_stats['avg_spend_per_block']:,} Sats"
                )
                print(f"  Win %: {group_stats['win_percentage']:.2%}")
                print(f"  Canonical %: {group_stats['canonical_percentage']:.2%}")
                print(f"  Orphan rate: {group_stats['orphan_rate']:.2%}")
                print(f"  Price ratio: {group_stats['price_ratio']} Sats/STX")

        # Generate and save HTML content
        html_content = generate_html(num_blocks, svg_string, stats)

        if len(args.block_counts) == 1:
            basename = "sample"
        else:
            basename = "index" if index == 0 else f"{num_blocks}"
        with open(f"output/{basename}.html", "w") as file:
            file.write(html_content)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Run the script in observer or command-line mode."
    )
    parser.add_argument(
        "--observer", action="store_true", help="Run in observer mode (as a server)"
    )
    parser.add_argument(
        "--print-stats",
        action="store_true",
        help="Print the stats to the console",
    )
    parser.add_argument(
        "--at-tip", type=int, help="Burn block height at which to analyze"
    )
    parser.add_argument(
        "config_path", nargs="?", help="Path to the miner configuration file"
    )
    parser.add_argument(
        "block_counts",
        nargs="*",
        type=int,
        default=[20, 50, 100],
        help="Number of blocks to analyze (optional, defaults to [20, 50, 100])",
    )

    args = parser.parse_args()

    if not args.config_path:
        parser.print_help()
        sys.exit(1)

    if args.observer:
        print("Running in observer mode...")
        run_server(args)
    else:
        run_command_line(args)
