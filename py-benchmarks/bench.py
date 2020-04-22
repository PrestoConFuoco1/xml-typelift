#!/usr/bin/env python3
import timeit

sizes  = [32, 64, 128, 256, 512, 1024]
prefix = '/i/p/migamake/xml-typelift/generated/customersOrders_'
cnt    = 10

for sz in sizes:
    print(f"{sz}", end='', flush=True)
    t = timeit.timeit(f"et.parse('{prefix}{sz:05d}Mb.xml')", setup="from lxml import etree as et", number=cnt)
    t /= cnt
    print(f",\t{t}")
