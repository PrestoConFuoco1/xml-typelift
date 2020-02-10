#!/bin/sh -e
stack run -- xml-typelift-cli --schema test/data/customersOrders.xsd > bench/generated/XMLSchema.hs
