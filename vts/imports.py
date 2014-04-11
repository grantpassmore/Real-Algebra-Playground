import sympy

import isym
import uni_vts
import z3rcf
import checker
import examples_parser

x = sympy.var('x')

def hook():
  'lt'
  p = x**6/60 - x**5/60 - x**2 - 6*x - 12
  #print isym.ts([], [p], [], [])
  eps = z3rcf.MkInfinitesimal('eps')
  li = [-12.0, -6.0, -1.0, 0, 0, -1/60.0, 1/60.0]
  terms = zip(li, range(len(li)))
  rs = z3rcf.MkRoots(li)
  reduce(lambda s, (c, p): s + c*rs[0]**p, terms, 0)
  return uni_vts.internal_ts([], [li], [], [])