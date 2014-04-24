import re

import z3rcf

def sign(v):
  return -1 if v < 0 else 1 if v > 0 else 0


def der(poly):
  return map(lambda (p, c): c*p, enumerate(poly))[1:]

def multiply(poly1, poly2):
  #print "poly1: %s" %poly1
  #print "poly2: %s" %poly2
  ret = []
  for power in range(len(poly1) + len(poly2) - 1):
    sum = 0
    #print "p_p: %s" %power
    for p1_power in range(len(poly1)):
      # contineu p1 power is too small
      if p1_power + len(poly2) <= power:
        continue
      # break p1 power is too big
      if p1_power > power:
        break
      #print "  p1_p: %s" %p1_power
      for p2_power in range(len(poly2)):
        # p2 power is too big given p1 power
        if p1_power + p2_power > power:
          break
        # try next value
        if p1_power + p2_power != power:
          continue
          
        # in here p1_power + p2_power = power
        sum += poly1[p1_power] * poly2[p2_power]
    ret.append(sum)
  return ret


def signed_prem(f, g):
  if f == []:
    return []

  if g == []:
    raise Exception("Division by zero polynomial")
  
  lc_f = f[-1]
  lc_g = g[-1]
  
  if lc_f == 0:
    return signed_prem(f[:-1], g)
    
  # can't change the sign of the remainder
  if lc_g < 0:
    lc_g = -lc_g
    lc_f = -lc_f
  
#  print "f: %s" %f
#  print "g: %s" %g
#  lc_gcd = sympy.gcd(lc_f, lc_g)
#  print "lc_gcd: %s" %lc_gcd

  # degree is smaller
  if len(f) < len(g):
#    gcd = abs(reduce(fractions.gcd, f))
#    gcd = reduce(sympy.gcd, f)
#    print "gcd: %s" %gcd
#    return map(lambda c: c / gcd, f)
    return f
  
  # might be faster to create a list and then fill it
  padding = [0] * (len(f) - len(g))
  
  # TODO again ask about precision
  # if isinstance(lc_f, int) and isinstance(lc_g, int):
    # coef = lc_f / float(lc_g)
  # else:
    # coef = lc_f / lc_g
    
  q_first_term_by_g = padding + map(lambda p: p, g)
  
  """print "f: %s" %f
  print "g: %s" %g
  print "lc_f: %s" %lc_f
  print "lc_g: %s" %lc_g
  print "coef: %s" %coef
  print "type: %s" %type(coef)"""
  
  subtracted = map(lambda (c1, c2): c1*lc_g - c2*lc_f
      , zip(f, q_first_term_by_g))
  return signed_prem(subtracted[:-1], g)



def dec_z3rcf_roots(poly, digits=30):
  rs = z3rcf.MkRoots(poly)
  reg = re.compile('-{0,1}[0-9\.]*')
  ds = map(lambda r: r.decimal(digits), rs)
#  print "ds: %s" %ds
  ret = map(lambda s: float(reg.match(s).group()), ds)
#  print ret
  return ret

def eval_poly(poly, point):
  return reduce(lambda s, (p, c): s + c*point**p, enumerate(poly), 0)

