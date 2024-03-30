[Praline](https://github.com/peterhj/praline)
is an exact parser from a subset of natural language
mathematics to an intermediate symbolic representation
language based on logical forms, also called Praline.
The Praline parser was implemented on a [dataset](#datasets)
derived from IMO shortlist geometry problem statements.
The latest snapshot of the parser produces roughly
121 gold parses out of 578 total reference sentences,
for a success rate of 21%.


## Instructions


### Building for testing and development

Note: These build instructions assume a unix-like system.

1.  Create a workspace directory, and clone this repository
    into the workspace:

        mkdir praline-workspace
        cd praline-workspace
        git clone https://github.com/peterhj/praline

2.  Run the bootstrap script in this repository to checkout
    the vendored dependencies into the workspace:

        cd praline
        ./bootstrap.sh

3.  The default Makefile target is for a release build:

        make

    or, you may target a debug build:

        make debug


### Running Praline on the IMO shortlist geometry reference set

The script for running the parser on the IMO shortlist
geometry dataset is at `tools/run_geom_r135.rs`.

    # release build:
    ./target/release/run_geom_r135

    # debug build:
    ./target/debug/run_geom_r135


## Datasets

The Praline parser was built using a reference dataset
of transcribed IMO shortlist geometry problems.
Additionally, the latest snapshot of the Praline parser
produces a dataset of _gold parses_ for a subset of the
natural language sentences in the reference dataset.


### IMO shortlist geometry reference dataset

The dataset consists of 578 sentences, in English LaTeX,
transcribed from 135 geometry problem statements from
the IMO shortlists of years 2006 to 2022 inclusive.
The complete dataset in JSON Lines format can be found
in this repository at the path `data/geom_r135.jsonl`.

Note: For pre-processing purposes, sentences in the
dataset have been normalized to use single spaces, and
also have a single space prepended.


### Gold parse set

The set of complete gold parses produced by the Praline
parser corresponding to the reference dataset are
available at the path
`data/geom_r135_gold_latest.jsonl`.

The latest snapshot of the parser produces 121 gold
parses from of a total of 578 reference sentences,
for a success rate of 21%.
