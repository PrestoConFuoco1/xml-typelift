#!/bin/bash

stack install xml-typelift:exe:xml-typelift-cli
xml-typelift-cli --schema /home/yuri/prog/haskell/xml/parse1/xml/shiporder1.xsd --main --unsafe > /home/yuri/prog/haskell/xml/parse1/xml/log1 2> /home/yuri/prog/haskell/xml/parse1/xml/errlog1 
cp /home/yuri/prog/haskell/xml/parse1/xml/log1 /home/yuri/prog/haskell/xml/parse1/app/XMLSchema.hs
