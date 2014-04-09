import sympy
import uni_vts

def convert(poly):
  poly = poly.expand()
  symbols = poly.free_symbols
  if len(symbols) > 1:
    raise Exception("more than one symbol")
  if len(symbols) == 0:
    raise Exception("implement constant")
  x = symbols.pop()
  
  sympy.LC(poly, x)
  # get the x terms
  xterms = poly.as_terms()[0]
  
  lrepr = map(lambda t: (t[1][0][0], t[1][1][0]), xterms)
  mrepr = {}
  for (c, p) in lrepr:
    mrepr[p] = c
  max_pow = sorted(mrepr.keys()).pop()

  pows = range(max_pow + 1)

  inf_repr = [mrepr[pow] if mrepr.has_key(pow) else 0 for pow in pows]
  return inf_repr
  

def ts(eq, lt):
  return uni_vts.internal_ts(map(convert, eq), map(convert, lt))
def vts(eq, lt):
  return uni_vts.internal_vts(map(convert, eq), map(convert, lt))