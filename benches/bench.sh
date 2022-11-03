#!/bin/sh
#
# Run all benchmarks and convert into markdown
#
# SOURCE: https://github.com/nu11ptr/criterion-table
#
# # SETUP
# ```
# $ cargo install cargo-criterion
# $ cargo install criterion-table
# ```
#

# A)
# cargo criterion --message-format=json | criterion-table > BENCHMARKS.md

# B)
# cargo criterion --output-format=quiet --message-format=json \
# 	| criterion-table > BENCHMARKS.md

# C)
cargo criterion --output-format=quiet --message-format=json > BENCHMARKS.json
cat BENCHMARKS.json | criterion-table > BENCHMARKS.md
