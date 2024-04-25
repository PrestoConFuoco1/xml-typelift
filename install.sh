#!/bin/bash

stack install xml-typelift:exe:xml-typelift-cli
xml-typelift-cli --isogen-naming --generate-lenses --schema /home/yuri/prog/haskell/xml/parse1/xml/shiporder1.xsd --toplevel shiporder --main --unsafe > /home/yuri/prog/haskell/xml/parse1/xml/log1 2> /home/yuri/prog/haskell/xml/parse1/xml/errlog1
cp /home/yuri/prog/haskell/xml/parse1/xml/log1 /home/yuri/prog/haskell/xml/parse1/app/XMLSchema.hs

