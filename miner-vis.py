#!/usr/bin/env python3

import argparse
import sqlite3
import sys
from graphviz import Digraph
import datetime
import re
import toml
from flask import Flask, request

default_color = "white"


def is_miner_tracked(miner_config, identifier):
    # Check if the miner is in the config and is tracked
    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info and miner_info.get("track", False):
        return True
    return False


def get_miner_color(miner_config, identifier):
    # Retrieve the color for the given miner identifier
    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info:
        return miner_info.get("color", default_color)
    return default_color


def get_miner_name(miner_config, identifier):
    # Retrieve the name for the given miner identifier
    miner_info = miner_config.get("miners", {}).get(identifier)
    if miner_info:
        return miner_info.get("name", identifier[0:8])
    return identifier[0:8]


class Commit:
    def __init__(
        self,
        block_header_hash,
        sender,
        burn_block_height,
        spend,
        sortition_id,
        parent=None,
        canonical=False,
    ):
        self.block_header_hash = block_header_hash
        self.sender = sender[1:-1]  # Remove quotes
        self.burn_block_height = burn_block_height
        self.spend = spend
        self.sortition_id = sortition_id
        self.parent = parent
        self.children = False  # Initially no children
        self.canonical = canonical

    def __repr__(self):
        return f"Commit({self.block_header_hash[:8]}, Burn Block Height: {self.burn_block_height}, Spend: {self.spend:,}, Children: {self.children})"


def get_block_commits_with_parents(db_file, last_n_blocks=1000):
    conn = sqlite3.connect(db_file)
    cursor = conn.cursor()

    # Pre-compute the maximum block height
    cursor.execute("SELECT MAX(block_height) FROM block_commits")
    max_block_height = cursor.fetchone()[0]
    lower_bound_height = max_block_height - last_n_blocks

    # Fetch the necessary data to build the graph
    query = """
    SELECT
        block_header_hash,
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
        block_height > ?
    ORDER BY
        block_height ASC
    """
    cursor.execute(query, (lower_bound_height,))
    raw_commits = cursor.fetchall()

    # Prepare dictionaries to hold the parent hashes and total spends
    parent_hashes = {}
    sortition_sats = {}
    commits = {}  # Track all nodes, by block_header_hash

    for (
        block_header_hash,
        apparent_sender,
        sortition_id,
        vtxindex,
        block_height,
        burn_fee,
        parent_block_ptr,
        parent_vtxindex,
    ) in raw_commits:
        parent = parent_hashes.get((parent_block_ptr, parent_vtxindex))
        if parent:
            commits[parent].children = True

        commits[block_header_hash] = Commit(
            block_header_hash,
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


def mark_canonical_blocks(db_file, commits):
    conn = sqlite3.connect(db_file)
    cursor = conn.cursor()

    tip = cursor.execute(
        "SELECT canonical_stacks_tip_hash FROM snapshots ORDER BY block_height DESC LIMIT 1;"
    ).fetchone()[0]

    while tip:
        commits[tip].canonical = True
        tip = commits[tip].parent


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
                node_label = f"{get_miner_name(miner_config, commit.sender)}\n{round(commit.spend/1000.0):,}K ({commit.spend/sortition_sats[commit.sortition_id]:.0%})"

                if is_miner_tracked(miner_config, commit.sender):
                    tracked_spend += commit.spend

                c.attr(
                    label=f"Burn Block Height: {commit.burn_block_height}\nTotal Spend: {sortition_sats[commit.sortition_id]:,}\nTracked Spend: {tracked_spend:,} ({tracked_spend/sortition_sats[commit.sortition_id]:.2%})"
                )

                # Initialize the node attributes dictionary
                node_attrs = {
                    "color": "blue" if commit.children else "black",
                    "fillcolor": get_miner_color(miner_config, commit.sender),
                    "penwidth": "4" if commit.children else "1",
                    "style": "filled,solid",
                }

                # Additional modifications based on conditions
                if not commit.canonical:
                    node_attrs["style"] = "filled,dashed"
                    node_attrs["penwidth"] = "1"

                # Check if the commit spent more than the alert_sats threshold
                if commit.spend > miner_config.get("alert_sats", 1000000):
                    node_attrs["fontcolor"] = "red"
                    node_attrs["fontname"] = "bold"

                # Now use the dictionary to set attributes
                c.node(commit.block_header_hash, node_label, **node_attrs)

                if commit.parent:
                    # If the parent is not the previous block, color the edge red
                    color = "black"
                    penwidth = "1"
                    if commits[commit.parent].burn_block_height != last_height:
                        color = "red"
                        penwidth = "4"
                    c.edge(
                        commit.parent,
                        commit.block_header_hash,
                        color=color,
                        penwidth=penwidth,
                    )

            last_height = block_height

    return dot.pipe(format="svg").decode("utf-8")


def collect_stats(miner_config, commits):
    tracked_commits_per_block = {}
    wins = 0
    for commit in commits.values():
        if is_miner_tracked(miner_config, commit.sender):
            # Keep an array of all tracked commits per block
            tracked_commits_per_block[
                commit.burn_block_height
            ] = tracked_commits_per_block.get(commit.burn_block_height, [])
            tracked_commits_per_block[commit.burn_block_height].append(commit.spend)

            # Count the number of wins
            if commit.children:
                wins += 1

    if len(tracked_commits_per_block) == 0:
        print("No tracked commits found")
        return {
            "avg_spend_per_block": 0,
            "win_percentage": 0,
        }

    # Print stats
    spend = 0
    for spends in tracked_commits_per_block.values():
        spend += sum(spends)

    return {
        "avg_spend_per_block": round(spend / len(tracked_commits_per_block)),
        "win_percentage": wins / len(tracked_commits_per_block),
    }


def generate_html(n_blocks, svg_content, stats):
    current_time = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # Use regex to replace width and height attributes in the SVG
    svg_content = re.sub(r'width="\d+pt"', 'width="100%"', svg_content)
    svg_content = re.sub(r'height="\d+pt"', 'height="100%"', svg_content)

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
        <h2>Statistics</h2>
        <table>
            <tr><th>Average Spend per Block</th><td>{stats['avg_spend_per_block']:,}</td></tr>
            <tr><th>Win Percentage</th><td>{stats['win_percentage']:.2%}</td></tr>
        </table>
        <h2>Block Commits</h2>
        <div class="responsive-svg">
            {svg_content}
        </div>
    </body>
    </html>
    """
    return html_content


def run_server(args):
    app = Flask(__name__)

    @app.route("/new_block", methods=["POST"])
    def new_block():
        print("Received new block notification")
        run_command_line(args)
        return "Command executed", 200

    app.run(host="0.0.0.0", port=8088)


def run_command_line(args):
    print("Generating visualization...", args)
    with open(args.config_path, "r") as file:
        miner_config = toml.load(file)

    for index, last_n_blocks in enumerate(args.block_counts):
        commits, sortition_sats = get_block_commits_with_parents(
            miner_config.get("db_path"), last_n_blocks
        )
        mark_canonical_blocks(miner_config.get("db_path"), commits)

        svg_string = create_graph(miner_config, commits, sortition_sats)

        stats = collect_stats(miner_config, commits)
        print(f"Avg spend per block: {stats['avg_spend_per_block']:,} Sats")
        print(f"Win %: {stats['win_percentage']:.2%}")

        # Generate and save HTML content
        html_content = generate_html(last_n_blocks, svg_string, stats)

        basename = "index" if index == 0 else f"{last_n_blocks}"
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
        "config_path", nargs="?", help="Path to the miner configuration file"
    )
    parser.add_argument(
        "block_counts",
        nargs="*",
        type=int,
        default=[20, 50, 100],
        help="List of block counts (optional, defaults to [20, 50, 100])",
    )

    args = parser.parse_args()

    if args.observer:
        print("Running in observer mode...")
        run_server(args)
    else:
        if not args.config_path:
            parser.print_help()
            sys.exit(1)

        print("Running in command-line mode...")
        run_command_line(args)
