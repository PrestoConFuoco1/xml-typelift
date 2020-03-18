#!/bin/sh -e

## Generate XML files for benchmarking

stack build xml-typelift:exe:mkxml

# place for generated files
mkdir -p tmp/generated

for i in `seq 0 7` ; do
    size=`echo "32 * 2^$i" | bc`
    fn="tmp/generated/customersOrders_`printf '%05i' $size`Mb.xml"
    echo "Generating ${fn}..."
    stack run mkxml -- $size $fn
done

