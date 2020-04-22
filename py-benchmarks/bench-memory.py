#!/usr/bin/env python3
from lxml import etree as et

prefix = '/i/p/migamake/xml-typelift/generated/customersOrders_'

@profile
def load():
    et.parse(f'{prefix}00032Mb.xml')
    et.parse(f'{prefix}00064Mb.xml')
    et.parse(f'{prefix}00128Mb.xml')
    et.parse(f'{prefix}00256Mb.xml')
    et.parse(f'{prefix}00512Mb.xml')
    et.parse(f'{prefix}01024Mb.xml')


if __name__ == '__main__':
    load()
