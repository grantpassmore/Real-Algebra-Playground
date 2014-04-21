import sympy
import uni_vts

def convert(poly):
  """Converts a sympy polynomial to list of coefficients. Where ith element
  corresponds to ith power in the polynomial, 
  list is of length degree(poly) + 1.
  When coefficients can be cast to int such that c == int(c), 
  then list of int is returned. 0 is converted to []
  
  Keyword arguments:
  poly -- polynomial to be converted (univariate)
  
  return -- list of coefficients
  """

  if isinstance(poly, int):
    if poly == 0:
      return []
    return [poly]

  symbols = poly.free_symbols
  if len(symbols) == 0:
    return convert_rationals_to_ints([poly])

  poly = poly.expand()

  if len(symbols) > 1:
    raise Exception("more than one symbol")
  x = symbols.pop()

  terms = poly.as_ordered_terms()

  leadterms = map(lambda t: t.leadterm(x), terms)

  intterms = map(lambda (c,p): (c,int(p)), leadterms)
  degree = intterms[0][1]
  pow_lookup = {p: c for (c,p) in intterms}

#  print "intterms: %s" %intterms
#  print "pow_lookup: %s" %pow_lookup

#  print "degree: %d" %degree

  coef_list = [pow_lookup[i] if pow_lookup.has_key(i) else 0 
               for i in range(degree + 1)]
#  print "coef_list: %s" %coef_list
#  print "equal: %s" %(coef_list ==  int_coefs)

  # TODO think of a better way to handle non ints
  return convert_rationals_to_ints(coef_list)

def convert_rationals_to_ints(coef_list):
  ints = filter(lambda c: isinstance(c, int), coef_list)
  rationals = filter(lambda c: isinstance(c, sympy.Rational), coef_list)
  if len(ints) + len(rationals) > len(coef_list):
    raise Exception("int's and rationals are not mutually exclusive")

  lcm = reduce(lambda x, y: sympy.lcm(x, y.q), rationals, 1)
  
  no_rationals = map(lambda x: x * lcm, coef_list)
  
  int_coefs = [int(x) if isinstance(x, sympy.Integer) else x 
               for x in no_rationals]




  if len(rationals) + len(ints) != len(coef_list):
#    print "not equal"
    print "coef_list: %s" %coef_list
    print "rationals: %s" %rationals  
    print "lcm: %s" %lcm
    print "int_coefs: %s" %int_coefs
    print "types: %s" %map(type, int_coefs)

    raise Exception("not rational")
    pass

  
  return int_coefs
  
def convert_back(lpoly):
  return sum(
    map(
      lambda (c, p): c*sympy.var('x')**p, 
      zip(lpoly, range(len(lpoly))))
  )
  

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
  
  return  uni_vts.internal_vts(converted_le, converted_lt, \
      converted_eq, converted_ne)
  
  
