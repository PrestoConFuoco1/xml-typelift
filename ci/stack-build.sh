#!/bin/bash

source ci/common.sh

# Build it
message "Build it"
export CI_GHC_ADDITIONAL_FLAGS="--system-ghc"
# Note: `--allow-different-user` flag is for debugging purpose,
# when running this script locally in developer's working directory
stack install --system-ghc --allow-different-user
stack build   --system-ghc --allow-different-user
stack test    --system-ghc --allow-different-user xml-typelift:test:unit-tests

# check that CLI application is working and output is reasonable
message "Check CLI"
stack exec -- xml-typelift-cli --version
stack exec -- xml-typelift-cli --help
stack exec -- xml-typelift-cli --schema test/data/customersOrders.xsd --types > types.hs
stack exec -- xml-typelift-cli --schema test/data/customersOrders.xsd > parser.hs
grep -z "\<data Customers.*= Customers {.*}" types.hs > /dev/null
grep -z "\<parseTopLevelToArray " parser.hs > /dev/null

message "Check generated code runs"
stack exec --system-ghc -- ghc types.hs
stack exec --system-ghc -- ghc parser.hs

# check that benchmarks is working (but limit for 10 minutes only because of slow benchmarking)
message "Check benchmarks"
timeout 30m stack bench --system-ghc xml-typelift:bench:proto-parsers-speed
