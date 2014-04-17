import z3rcf
import sympy
import isym # used in checking


import matrix_of_signs

class ConditionExc(Exception):
  def __init__(self, root, poly, value):
    self.root = root
    self.poly = poly
    self.value = value
  def __str__(self):
    #print "root: %s" %self.root
    #print "poly: %s" %self.poly
    return repr(self.value)


def internal_ts(eq, lt):
  for equality in eq:
    print "quality %s" %equality
    roots = z3rcf.MkRoots(equality)
    print "roots: %s" %roots
    for root in roots:
      try:
        evaluate(root, eq, lt)
        print "good"
        return True
      except ConditionExc as e:
        print e
  
  eps = z3rcf.MkInfinitesimal('eps')
  for less_than in lt:
    roots = z3rcf.MkRoots(less_than)
    for root in roots:
      try:
        evaluate(root + eps, eq, lt)
        print "good"
        return True
      except ConditionExc as e:
        print e
  try:
    evaluate(-1 / eps, eq, lt)
    print "good"
    return True
  except ConditionExc as e:
    print e
  return False

def internal_ts(le, lt, eq, ne):
  """Determines the satisfiability of constraints by calculating polynomials on 
  points on all possible (solutions set) intervals
  
  Keyword arguments:
  le -- list of polynomial coefficients that are <= 0 (z3rcf format)
  lt -- list of polynomial coefficients that are < 0 (z3rcf format)
  eq -- list of polynomial coefficients that are = 0 (z3rcf format)
  ne -- list of polynomial coefficients that are != 0 (z3rcf format)
  
  return boolean corresponding to satisfiability of constraints
  """
  
  # iterate over all points that might be end points of closed intervals
  for equality in (eq + le):
    roots = z3rcf.MkRoots(equality)
    for root in roots:
      try:
        evaluate(root, le, lt, eq, ne)
        #print "good"
        return True
      except ConditionExc as e:
        pass #print e
  
  eps = z3rcf.MkInfinitesimal('eps')
  
  #iterate over all lower bounds of open intervals
  for less_than in lt + ne:
    roots = z3rcf.MkRoots(less_than)
    for root in roots:
      try:
        evaluate(root + eps, le, lt, eq, ne)
        #print "good"
        return True
      except ConditionExc as e:
        pass #print e
  
  # check the -infinity value
  try:
    evaluate(-1 / eps, le, lt, eq, ne)
    #print "good"
    return True
  except ConditionExc as e:
    pass #print e
  return False
  
  
def internal_vts(le, lt, eq, ne):
  sign_lookup = sign_conditions_lookup(le, lt, eq, ne)
  all_polies = (le + lt + eq + ne)
  # print "internal"

  for exact_poly in (le + eq):
    # print "exact_poly: %s" %exact_poly
    roots = z3rcf.MkRoots(exact_poly)
    droots = get_discri_der_signs(roots, exact_poly)
    map(lambda d: d.set_origin_poly(exact_poly), droots)
    
    for droot in droots:
      # print "droot: %s" %droot
      formula_value = evaluate_on_sign_assignment(droot, all_polies, sign_lookup)
      # print "formula_value: %s" %formula_value
      if formula_value:
        return True
    
  for e_close_poly in lt + ne:
    roots = z3rcf.MkRoots(e_close_poly)
    droots = get_discri_der_signs(roots, e_close_poly)
    map(lambda d: d.set_origin_poly(e_close_poly), droots)
    
    for droot in droots:
      # print "droot: %s" %droot
      formula_value = e_close_evaluate_on_sign_assignment(
          droot, all_polies, sign_lookup)
      # print "formula_value: %s" %formula_value
      if formula_value:
        return True
  
  for poly in all_polies:
    # print poly
    # print sign
    # print sign_lookup[make_poly_hashabel(poly)]
    sign = sign_func(poly[-1] * (-1)**((len(poly) - 1)%2))
    if not sign in sign_lookup[make_poly_hashabel(poly)]:
      return False
  
  return True
  

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
  
def make_product_list(polies):
  """Makes the list of products such that if polies = [p1, p2, p3]
  then returns [p1**i * p2**k * p3**k] for (i, j, k) in {0, 1, 2}**3
  (0, 0, 0)<(0, 0, 1)<(0, 0, 2)< ..  <(0, 1, 0)< .. <(1, 0, 0)< .. <(2, 2, 2)
  """
  if polies == []:
    return [[1]]
  
  head = polies[0]
  square = multiply(head, head)
  rest = polies[1:]
  
  #print head
  #print polies
  
  rest_list = make_product_list(rest)
  #print rest_list
  
  acc = []
  for power in [0, 1, 2]:
    for product in rest_list:
      if power == 0:
        acc.append(product)
        continue
      if power == 1:
        acc.append(multiply(product, head))
        continue
      if power == 2:
        acc.append(multiply(product, square))
        continue
  #print len(acc)
  return acc

def signed_pseudo_remainder(f, g):
  if f == []:
    return []

  if g == []:
    raise Exception("Division by zero polynomial")
  
  lc_f = f[-1]
  lc_g = g[-1]
  
  if lc_f == 0:
    return signed_pseudo_remainder(f[:-1], g)
    
  # can't change the sign of the remainder
  if lc_g < 0:
    lc_g = -lc_g
    lc_f = -lc_f
  
  if len(f) < len(g):
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
  
  subtracted = map(lambda (c1, c2): c1*lc_g - c2*lc_f, zip(f, q_first_term_by_g))
  return signed_pseudo_remainder(subtracted[:-1], g)

  
def logger(f):
  def wrapper(*args, **kwargs):
    global log
#    print log
    if log:
      print "calling %s with args:%s, kwargs:%s" %(f.__name__, args, kwargs)
    return f(*args, **kwargs)
  return wrapper


def signed_remainder_sequence(p, q):
  """Calculates the signed remainder sequence of two polynomials
  Uses pseudo remainder

  Keyword arguments:
  p -- first polynomial in the sequence
  q -- second polynomial in the sequence

  return -- signed remainder sequence
  """
  # print "running"

  rem = signed_pseudo_remainder(p, q)
  # srem = sympy.div(isym.convert_back(p), isym.convert_back(q), x)[1]
  # print (srem - isym.convert_back(rem)).expand()
  if rem == []:
    return [p, q]
    
  neg_rem = map(lambda p: -p, rem)
  # print rem
  sequence = signed_remainder_sequence(q, neg_rem)
  sequence.insert(0, p)
  return sequence

def signed_remainder_cauchy_index(p, q):
  """Calculates the cauchy index by using signed remainder sequence
  
  Keyword arguments:
  p -- p part of q / p 
  q -- q part of q / p 
  
  return -- cauchy index (in interval (-inf, +inf))
  """
    
  if q == []:
    return 0
  
  sequence = signed_remainder_sequence(p, q)
  
  neg_inf = map(lambda p: p[-1] * (-1)**((len(p) - 1)%2), sequence)
  pos_inf = map(lambda p: p[-1], sequence)
  
  # for poly in map(isym.convert_back, sequence):
    # print "%d. %s" %(map(isym.convert_back, sequence).index(poly), poly)
  
  # print "neg_inf: %s" %neg_inf
  # print "pos_inf: %s" %pos_inf
  
  f_neg_inf = filter(lambda c: c != 0, neg_inf)
  f_pos_inf = filter(lambda c: c != 0, pos_inf)
  
  neg_jumps = map(lambda (p, n): p*n, zip(f_neg_inf[:-1], f_neg_inf[1:]))
  neg_changes = len(filter(lambda c: c < 0, neg_jumps))
  
  pos_jumps = map(lambda (p, n): p*n, zip(f_pos_inf[:-1], f_pos_inf[1:]))
  pos_changes = len(filter(lambda c: c < 0, pos_jumps))
  
  return neg_changes - pos_changes
  

log = False
def tarski_query(p, q):
  """Computers the tarksi query of p, q - i.e. sums over q(x) on such x-s 
  that p(x) == 0.
  
  Keyword arguments:
  p -- polynomials at whose roots the tarksi query is inspected
  q -- signs that are inspected in tarksi query

  return tarski query value
  """
  
  # print 'tarksi query'
  p_der = derivative(p)
  # print (sympy.diff(isym.convert_back(p), sympy.var('x')) - isym.convert_back(p_der)).expand()
  
  global log
  log = True
  ret = signed_remainder_cauchy_index(p, multiply(p_der, q))
  
  # sp = isym.convert_back(p)
  # sq = isym.convert_back(q)
  # rs = sympy.solve(sp, sympy.var('x'))
  # sum = 0
  # for r in rs:
    # sum += sympy.sign( sq.subs([(sympy.var('x'), r)]) )
  
  # #test this
  # #[24, -50, 35, -10, 1], [-50, 170, -220, 134, -38, 4]
  
  # # print "ret: %s" %ret
  # # print "sum: %s" %sum
  # print "dif: %s" %(ret - sum)
  # if ret != sum:
    # print "rs: %s" %rs
    # print "got: %s" %ret
    # print "actual: %s" %sum
    # print sp
    # print sq
    # print
    
    # raise Exception("different sums: ")
  
  return ret

def pick_sign_of_goal(polies, discDerSign, c_matrix):
  # print
  
  off_values = {0: 0, 1: 1, -1: 2}
  
  total = 3**len(polies)
  
  total_shift = 0
  
  # print "total: %d" %len(polies)
  for poly in polies[:-1]:
    # print "%d. poly: %s" %(polies.index(poly), poly)
    step = total / 3**(polies.index(poly) + 1)
    sign = discDerSign.get_sign(poly)
    
    # print "step: %s" %step
    # print "sign: %s" %sign
    total_shift += step * off_values[sign]
    # print
  # print
  
  # print "total_shift: %s" %total_shift
  
  for sign in off_values:
    value = c_matrix[total_shift + off_values[sign]]
    if value == 1:
      return sign
    if not value in [0, 1]:
      raise Exception("table had a value that was neither 0 or 1 (%s)" %value)
  raise Exception("no entry in the table was with count 1")
  
def sign_func(v):
  return -1 if v < 0 else 1 if v > 0 else 0

def get_sign_by_direct_calc(polies, discDerSign):
  rs = z3rcf.MkRoots(discDerSign.origin)
  
  good_values = []
  for r in rs:
    good = True
    for poly in polies[:-1]:
      p_sign = sign_func(evaluate_poly(poly, r))
      if p_sign != discDerSign.get_sign(poly):
        good = False
        break
    if good:
      good_values.append(sign_func(evaluate_poly(polies[-1], r)))
      
  # must be impossible
  if len(good_values) != 1:
    raise Exception("didn't have a good value")
  return good_values[0]

def check_powers(list_products, polies):
  if len(polies) != 3:
    return
  return 
  print "CHECKING POWERS"
  c_back = lambda p: isym.convert_back(p)
  ps =  map(c_back, polies)
  products = map(c_back, list_products)
  print "ps[0]: %s" %ps[0]
  print "ps[1]: %s" %ps[1]
  print "ps[2]: %s" %ps[2]
  print "products[i]: %s" %products[1]
  print "check: %s" %(products[24] - (ps[0]**2 * ps[1]**2 * ps[2]**0)).expand()
  print "check: %s" %(products[25] - (ps[0]**2 * ps[1]**2 * ps[2]**1)).expand()
  print "check: %s" %(products[26] - (ps[0]**2 * ps[1]**2 * ps[2]**2)).expand()
    
  print
def evaluate_single_on_sign_assignment(discDerSign, goal):
  if goal == discDerSign.origin:
    return 0
    
  # print "origin: %s" %discDerSign.origin
  # sympy.pprint( isym.convert_back(discDerSign.origin))
  
  # sder =  map(isym.convert_back, discDerSign.get_all_polies())
  # print sder
  # print map(lambda p: p.subs([(sympy.var('x'), 4)]), sder)
  # print "discDerSign: %s" %discDerSign
  # print "goal: %s" %goal
  
  
  polies = discDerSign.get_all_polies() + [goal]
  
  
  M_inv = matrix_of_signs.get_matrix_inverse(len(polies))
  
  """powers = [[]]
  for s in range(len(polies)):
    acc = []
    for i in range(3):
      copy = list(map(lambda l: list(l), powers))
      map(lambda l: l.insert(0, i), copy)
      acc += copy
    powers = acc
  
  # pads the powers by their position on the list  
  indexed_powers = map(lambda l: zip(range(len(l)), l), powers)
  
  product_polies = []
  for power in indexed_powers:
    # passprint power
    pass
  """

  product_list = make_product_list(polies)
  
  check_powers(product_list, polies)
  
  # calculate tarski query on products
  # make column vector of values
  taq_column = sympy.Matrix(
    map(lambda poly: [tarski_query(discDerSign.origin, poly)], product_list)
  )
  
  
  # multiply inverse with column
  c_matrix = M_inv * taq_column
  
  # print polies
  # print "len(polies): %s" %len(polies)
  # print "len(c_matrix): %s" % len(c_matrix.col(0))
  # print discDerSign
  s = lambda i: i if i < 2 else -1
  for i in range(len(c_matrix.col(0))):
    #print "(%+d, %+d, %+d, %+d) \t" %(s(i/27%3), s(i/9%3), s(i/3%3), s(i%3)),
    # print "(%+d, %+d, %+d) \t" %(s(i/9%3), s(i/3%3), s(i%3)),
    # print c_matrix[i, 0]
    pass
  
  # TODO remove
  # calculate the sign to check 
  # calc_sign = get_sign_by_direct_calc(polies, discDerSign)
  # print "calc_sign: %s" %calc_sign
  # return calc_sign
  
  
  # pick the right root based on conditions
  # print c_matrix
  goal_sign = pick_sign_of_goal(polies, discDerSign, c_matrix)
  # print "goal_sign: %s" %goal_sign
  
  
  
  # TODO also remove (see calculation)
  # if calc_sign != goal_sign:
    # raise Exception("calculated one differed from goal_sign")
  
  return goal_sign

#TODO change this
def make_poly_hashabel(poly):
  return tuple(map(str, poly))

def sign_conditions_lookup(le, lt, eq, ne):
  sign_lookup = {}
  
  for p in (le + lt + eq + ne):
    sign_lookup[make_poly_hashabel(p)] = {-1, 0, 1}
  for p in le:
    sign_lookup[make_poly_hashabel(p)] = sign_lookup[make_poly_hashabel(p)].intersection({-1, 0})
  for p in lt:
    sign_lookup[make_poly_hashabel(p)] = sign_lookup[make_poly_hashabel(p)].intersection({-1})
  for p in eq:
    sign_lookup[make_poly_hashabel(p)] = sign_lookup[make_poly_hashabel(p)].intersection({0})
  for p in ne:
    sign_lookup[make_poly_hashabel(p)] = sign_lookup[make_poly_hashabel(p)].intersection({-1, 1})
  return sign_lookup

def e_close_evaluate_single_on_sign_assignment(discDerSign, poly):
  if poly == []:
    return 0
  current = evaluate_single_on_sign_assignment(discDerSign, poly)
  if current != 0:
    # print "current: %s" %current
    return current
  return e_close_evaluate_single_on_sign_assignment(
      discDerSign, derivative(poly)
  )
  
def e_close_evaluate_on_sign_assignment(discDerSign, all_polies, sign_lookup):
  # print "========"
  # print "evaling at: %s" %discDerSign
  # print "evaling at: %s" %isym.convert_back(discDerSign.origin)
  for poly in all_polies:
    sign = e_close_evaluate_single_on_sign_assignment(discDerSign, poly)
    # print "e_close: %s" %poly
    # print "sign: %s" %sign
    
    if not sign in sign_lookup[make_poly_hashabel(poly)]:
      return False
  return True
  
def evaluate_on_sign_assignment(discDerSign, all_polies, sign_lookup):
  for poly in all_polies:
    sign = evaluate_single_on_sign_assignment(discDerSign, poly)
    # print "poly: %s" %poly
    # print "sign: %s" %sign
    # print sign_lookup[make_poly_hashabel(poly)]
    if not sign in sign_lookup[make_poly_hashabel(poly)]:
      return False
  return True

class DiscDerSigns:

  def __init__(self, point):
    self.point = point
    self.neg_polies, self.zer_polies, self.pos_polies = [], [], []
    self.all_polies = []
    self.__lookup = {}
  
  def add_pos_poly(self, poly):
    self.pos_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[make_poly_hashabel(poly)] = 1
    
  def add_neg_poly(self, poly):
    self.neg_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[make_poly_hashabel(poly)] = -1
    
  def add_zer_poly(self, poly):
    self.zer_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[make_poly_hashabel(poly)] = 0
    
  def get_all_polies(self):
    return self.all_polies
    
  def set_origin_poly(self, poly):
    self.origin = poly
    #self.__add_poly_to_all_polies(poly)
    #self.__lookup[make_poly_hashabel(poly)] = 0
    
  def __add_poly_to_all_polies(self, poly):
    if poly in self.all_polies:
      raise "poly already there"
    self.all_polies.append(poly)
    
  def get_sign(self, poly):
    return self.__lookup[make_poly_hashabel(poly)]
    
  def __repr__(self):
    #return '[\npoint: %s\n  <:%s\n  0:%s\n  >:%s\n]' \
    #    %(self.point, self.neg_polies, self.zer_polies, self.pos_polies)
    return '[point: %s [<%s, =%s, >%s]]' \
        %(self.point.decimal(), len(self.neg_polies), 
        len(self.zer_polies), len(self.pos_polies))

def derivative(poly):
  coef_pows = zip(poly, range(len(poly)))[1:]
  return map(lambda (c, p): c*p, coef_pows)
    
def get_discri_der_signs(roots, exact_poly):
  if len(roots) == 0:
    return []
  if len(roots) == 1:
    return [DiscDerSigns(roots[0])]
  
  der = derivative(exact_poly)
  
  zero_roots, pos_roots, neg_roots = ([], [], [])
  for root in roots:
    der_value = evaluate_poly(der, root)
    
    # TODO ask Grant if library supports this kind of sieve
    if der_value > 0:
      pos_roots.append(root)
      continue
    if der_value < 0:
      neg_roots.append(root)
      continue
    zero_roots.append(root)
    
  
  ret = []
  if not len(zero_roots) == 0:
    discDerSigns = get_discri_der_signs(zero_roots, der)
    if not len(zero_roots) == len(roots):
      map(lambda p: p.add_zer_poly(der), discDerSigns)
    ret +=  discDerSigns
  
  #print "len(zero_roots): %s" %len(zero_roots)
  #print "len(ret): %s" %len(ret)
  
  if not len(pos_roots) == 0:
    discDerSigns = get_discri_der_signs(pos_roots, der)
    if not len(pos_roots) == len(roots):
      map(lambda p: p.add_pos_poly(der), discDerSigns)
    ret +=  discDerSigns
    
  #print "len(pos_roots): %s" %len(pos_roots)
  #print "len(ret): %s" %len(ret)
  
  if not len(neg_roots) == 0:
    discDerSigns = get_discri_der_signs(neg_roots, der)
    if not len(neg_roots) == len(roots):
      map(lambda p: p.add_neg_poly(der), discDerSigns)
    ret +=  discDerSigns
  
  #print "len(neg_roots): %s" %len(neg_roots)
  #print "len(ret): %s" %len(ret)
  
  
  #print "len(ret): %s" %len(ret)
  return ret

class EvalStr:
  def __init__(self, condition, msg):
    self.condition = condition
    self.msg = msg

__eq_str = EvalStr(lambda p: p == 0, 'Not equal to zero')
__lt_str = EvalStr(lambda p: p < 0, 'Not less than zero')
__le_str = EvalStr(lambda p: p <= 0, 'Not less or equal to zero')
__ne_str = EvalStr(lambda p: p != 0, 'Equal to zero')

def evaluate(root, eq, lt):
  print "evaluating with x = %s" %root
  r_str = map(lambda e: (e, __eq_str), eq) + \
    map(lambda e: (e, __lt_str), lt)
  for (poly, strategy) in r_str:
    print "  poly: %s" %poly
    terms = zip(poly, range(len(poly)))
    sum = reduce(lambda s, (c, p): s + c*root**p, terms, 0)
    print "  term values: %s" %map(lambda (c, p): c*root**p, terms)
    print "  sum: %s" %sum
    if not strategy.condition(sum):
      raise ConditionExc(root, poly, strategy.msg)

def evaluate_poly(poly, point):
  terms = zip(poly, range(len(poly)))
  return reduce(lambda s, (c, p): s + c*point**p, terms, 0)

def evaluate(point, le, lt, eq, ne):
  """Evaluate relations on specific point
  
  Keyword arguments:
  point -- point on which the relations are checked
  le -- list of polynomial coefficients that are <= 0 (z3rcf format)
  lt -- list of polynomial coefficients that are < 0 (z3rcf format)
  eq -- list of polynomial coefficients that are = 0 (z3rcf format)
  ne -- list of polynomial coefficients that are != 0 (z3rcf format)
  
  return -- True if all constraints are satisfied on the point
  """
  print "evaluating with x = %s" %point.decimal(5)
  r_str = map(lambda e: (e, __le_str), le) + \
      map(lambda e: (e, __lt_str), lt) + \
      map(lambda e: (e, __eq_str), eq) + \
      map(lambda e: (e, __ne_str), ne)
      
  for (poly, strategy) in r_str:
    #print "  poly: %s" %poly
    evaluate_poly(poly, point)
    #print "  term values: %s" %map(lambda (c, p): c*point**p, terms)
    #print "  sum: %s" %sum
    if not strategy.condition(sum):
      raise ConditionExc(point, poly, strategy.msg)
      
def evaluate_vts_root(root, eq, lt):
  print "evaling root: %s" % root
