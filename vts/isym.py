import sympy
import uni_vts

def convert(poly):
  """Converts a sympy polynomial to list of coefficients. Where ith element
  corresponds to ith power in the polynomial, list is of length degree(poly).
  
  Keyword arguments:
  poly -- polynomial to be converted (univariate)
  
  return -- list of coefficients
  """
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


def ts(le, lt, eq, ne):
  """Determines the satisfiability of the constraints by term substitution.
  
  Keyword arguments:
  le -- polynomials that are <= 0 (sympy format, univariate)
  lt -- polynomials that are < 0 (sympy format, univariate)
  eq -- polynomials that are = 0 (sympy format, univariate)
  ne -- polynomials that are != 0 (sympy format, univariate)
  
  return boolean corresponding to satisfiability of constraints
  """
  converted_le = map(convert, le)
  converted_lt = map(convert, lt)
  converted_eq = map(convert, eq)
  converted_ne = map(convert, ne)
  
  """
  print converted_le
  print converted_lt
  print converted_eq
  print converted_ne
  """
  return uni_vts.internal_ts(converted_le, converted_lt, \
      converted_eq, converted_ne)
  #return uni_vts.internal_ts(map(convert, eq), map(convert, lt))
  
def vts(le, lt, eq, ne):
  converted_le = map(convert, le)
  converted_lt = map(convert, lt)
  converted_eq = map(convert, eq)
  converted_ne = map(convert, ne)
  
  print uni_vts.internal_vts(converted_le, converted_lt, \
      converted_eq, converted_ne)
  
  