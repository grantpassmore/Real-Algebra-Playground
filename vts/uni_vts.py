from itertools import imap, chain
from functools import partial

import z3rcf
import sympy
import isym # used in checking

import matrix_of_signs
import utils
import prog_printer as prog

  
def internal_vts(le, lt, eq, ne):
  """Decides whether polynomials in lists le, lt, ... can satisfy relations
  <= 0, < 0, = 0, != 0 simulatationsly.

  Keyword arguments:
  le -- list of polynomials that are <= 0
  lt -- list of polynomials that are < 0
  eq -- list of polynomials that are = 0
  ne -- list of polynomials that are != 0
  
  return -- True if relations can be satisfied.
  """


  # make the sign lookup
  sign_lookup = sign_conditions_lookup(le, lt, eq, ne)
  all_polies = (le + lt + eq + ne)

  # iterate over polynomials where exact root is used in evaluation
  for exact_poly in (le + eq):
    prog.p("exact_poly: %s" %exact_poly)
    
    # all roots as sign assignement on derivatives
    droots = get_roots_as_dds(exact_poly)
    prog.inc()
    for droot in droots:
      # print "droot: %s" %droot
      # construct a evaluator corresponding to derivatives sign assignment
      evaluator = partial(evaluate_single_on_sign_assignment, droot)

      # evaluate all polynomials
      formula_value = eval_all_on_dds(evaluator, all_polies, sign_lookup)
      
      # print "formula_value: %s" %formula_value
      if formula_value:
        prog.dec()
        return True
    prog.dec()
  # iterator over polynomials where root + eps is used
  # analoguous to pervious loop
  for e_close_poly in lt + ne:
    prog.p("e_close_poly: %s" %e_close_poly)
    droots = get_roots_as_dds(e_close_poly)
    prog.inc()
    for droot in droots:
      # print "droot: %s" %droot
      evaluator = partial(e_close_evaluate_single_on_sign_assignment, droot)
      formula_value = eval_all_on_dds(evaluator, all_polies, sign_lookup)
      
      # print "formula_value: %s" %formula_value
      if formula_value:
        prog.dec()
        return True
    prog.dec()
  # evaluate polynomials on -infinity
  for poly in all_polies:
    sign = utils.sign(poly[-1] * (-1)**((len(poly) - 1)%2))
    if not sign in sign_lookup[utils.hashable(poly)]:
      return False
  #no relation was unsatified on -infinity
  return True
  

def make_product_list(polies):
  """Makes the ordered list of product of the elements in polies.
  Products are ordered by powers (0, 1, 2, and 0 < 1 < 2, the elements are 
  compared by power of the first element of polies, then second and so forth.
  starts with powers 0,.., 0 and ends with 2, .., 2
  
  Keyword arguments:
  polies -- list of polies that are factors

  return -- list of products
  """
  if polies == []:
    return [[1]]
  
  head = polies[0]
  square = utils.multiply(head, head)
  rest = polies[1:]
  
  #print head
  #print polies
  
  rest_list = make_product_list(rest)

  pow0 = imap(lambda p: p, rest_list)
  pow1 = imap(lambda p: utils.multiply(p, head), rest_list)
  pow2 = imap(lambda p: utils.multiply(p, square), rest_list)

  return list(chain(pow0, pow1, pow2))

  
def signed_remainder_sequence(p, q):
  """Calculates the signed remainder sequence of two polynomials (p is first
  and q is the second element in the sequence).
  Uses pseudo remainder

  Keyword arguments:
  p -- first polynomial in the sequence
  q -- second polynomial in the sequencen

  return -- signed remainder sequence
  """
  # print "running"

  rem = utils.signed_prem(p, q)
  # srem = sympy.div(isym.convert_back(p), isym.convert_back(q), x)[1]
  # print (srem - isym.convert_back(rem)).expand()
  if rem == []:
    return [p, q]

  neg_rem = map(lambda p: -p, rem)
  # print rem

  sequence = signed_remainder_sequence(q, neg_rem)

  # TODO:1 check which one is more efficient
  return chain([p], sequence)
  sequence.insert(0, p)
  return sequence

def signed_remainder_cauchy_index(p, q):
  """Calculates the cauchy index by using signed remainder sequence
  
  Keyword arguments:
  p -- p part of q / p 
  q -- q part of q / p 
  
  return -- cauchy index (in interval (-inf, +inf))
  """
  
  # [] is zero
  if q == []:
    return 0
  
  #TODO:1 conversion to list is neaded if sequence is generator
  sequence = list(signed_remainder_sequence(p, q))

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
  

def tarski_query(p, q):
  """Computers the tarksi query of p, q - i.e. sums over q(x) on such x-s 
  that p(x) == 0.
  
  Keyword arguments:
  p -- polynomials at whose roots the tarksi query is inspected
  q -- signs that are inspected in tarksi query

  return -- value of tarski query
  """
  
  p_der = utils.der(p)
  
  ret = signed_remainder_cauchy_index(p, utils.multiply(p_der, q))

  return ret
  # TODO remove this
  p_roots = z3rcf.MkRoots(p)
  values = map(lambda p: utils.eval_poly(q, p), p_roots)
  calc = len(filter(lambda c: c > 0, values)) - \
         len(filter(lambda c: c < 0, values))

  if calc != ret:
    print "p: %s" %p
    print "q: %s" %q
    print "sp: %s" %isym.convert_back(p)
    print "sq: %s" %isym.convert_back(q)
    print "ret: %s" %ret
    print "calc: %s" %calc
    raise Exception("calc and ret weren't equal")
  
  return ret

def pick_sign_of_goal(polies, discDerSign, c_matrix):
  """Picks the sign of the goal polynomial based on c_matrix

  Keyword arguments:
  polies -- list of polynomials appearing in derivatives sign assigment and
  the goal polynomial (goal is last)
  discDerSign - discirminating derivatives sign assignement for some root
  c_matrix -- matrix of counts corresponding to sign determination algorithm
  (single column matrix)

  return -- sign of the goal polynomial
  """

  # mapping between signs and shifts
  off_values = {0: 0, 1: 1, -1: 2}
  
  # total length of the column matrix
  total = 3**len(polies)
  
  # accumulated shift
  total_shift = 0
  

  for poly in polies[:-1]:
    # print "%d. poly: %s" %(polies.index(poly), poly)

    # step corresponding to polynomial place in the matrix
    step = total / 3**(polies.index(poly) + 1)
    # sign in aign assigment
    sign = discDerSign.get_sign(poly)

    # print poly
    # print "step: %s" %step
    # print "sign: %s" %sign
    

    total_shift += step * off_values[sign]
  # print "total_shift: %s" %total_shift
  
  goal_sign = None
  # itarate possible signs
  for sign in off_values:
    # inspect the count
    count = c_matrix[total_shift + off_values[sign]]
    if count == 1:
      # only one should be 1
      if goal_sign != None:
        raise Exception("multiple possible signs in matrix")
      goal_sign =  sign
      # since it was disciminating it should be either 0 or 1
    if not count in [0, 1]:
      raise Exception("table had a count that was neither 0 or 1 (%s)" %count)
  # count must be 1 on one case
  if goal_sign == None:
    s = "\ngoal: %s\n, dds: %s" %(polies[-1], discDerSign)
    raise Exception("no entry in the table was with count 1" + s)
  return goal_sign

# TODO move or delete
def get_sign_by_direct_calc(polies, discDerSign):
  rs = z3rcf.MkRoots(discDerSign.origin)
  
  good_values = []
  for r in rs:
    good = True
    for poly in polies[:-1]:
      p_sign = utils.sign(utils.eval_poly(poly, r))
      if p_sign != discDerSign.get_sign(poly):
        good = False
        break
    if good:
      good_values.append(utils.sign(utils.eval_poly(polies[-1], r)))
      
  # must be impossible
  if len(good_values) != 1:
    raise Exception("didn't have a good value")
  return good_values[0]

def evaluate_single_on_sign_assignment(discDerSign, poly):
  """Evaluate a polynonomial on a specific point

  Keyword arguments:
  discDerSign -- derivative sign assignment (point is reprsented by this)
  poly -- polynomial to be evaluated

  return -- sign of the poly on discDerSign + eps
  """
  

  prog.p("evaling %s" %poly)
  # origin is zero on der sign assignment
  if poly == discDerSign.origin:
    return 0
  
  polies = discDerSign.get_all_polies() + [poly]

  # inverse of matrix of signs
  M_inv = matrix_of_signs.get_matrix_inverse(len(polies))

  product_list = make_product_list(polies)
  
  # calculate tarski query on products
  # make column vector of values
  taq_column = sympy.Matrix(
    map(lambda poly: [tarski_query(discDerSign.origin, poly)], product_list)
  )
  
  # multiply inverse with column to get counts
  c_matrix = M_inv * taq_column

  poly_sign = pick_sign_of_goal(polies, discDerSign, c_matrix)
  
  return poly_sign

def e_close_evaluate_single_on_sign_assignment(discDerSign, poly):
  """Evaluate a polynonomial on e-close (+eps) region on a specific point

  Keyword arguments:
  discDerSign -- derivative sign assignment (point is reprsented by this)
  poly -- polynomial to be evaluated

  return -- sign of the poly on discDerSign + eps
  """

  if poly == []:
    return 0
  current = evaluate_single_on_sign_assignment(discDerSign, poly)
  if current != 0:
    # print "current: %s" %current
    return current
  return e_close_evaluate_single_on_sign_assignment(
      discDerSign, utils.der(poly)
  )
    
def eval_all_on_dds(single_evaluator, all_polies, sign_lookup):
  """Evaluates all polynomials on a specific value.
  
  Keyword arguments:
  single_evaluator -- function that returns the sign on point (curried 
  argument) of a polynomial.
  all_polies -- all polynomials that must satisfy sign_lookup.
  sign_lookup -- mapping from polies to allowed signs.

  return -- True if all polynomials satisfy signs allowed in sign_lookup.
  """

  poly_sign = lambda p: single_evaluator(p)
  # function that returns True if poly_sign satisfies sign_lookup
  sat = lambda p: poly_sign(p) in sign_lookup[utils.hashable(p)]
  return all(imap(sat, all_polies))

def sign_conditions_lookup(le, lt, eq, ne):
  """Creates a dictonary between polynomials and allowed signs

  Keyword arguments:
  le -- list of polynomials that are <= 0
  lt -- list of polynomials that are < 0
  eq -- list of polynomials that are = 0
  ne -- list of polynomials that are != 0

  return -- dictionary that maps polynomials to signs
  """

  sign_lookup = {}
  
  # allow all signs
  for p in (le + lt + eq + ne):
    sign_lookup[utils.hashable(p)] = {-1, 0, 1}

  # filter constrained signs
  for p in le:
    sign_lookup[utils.hashable(p)] = \
        sign_lookup[utils.hashable(p)].intersection({-1, 0})
  for p in lt:
    sign_lookup[utils.hashable(p)] = \
        sign_lookup[utils.hashable(p)].intersection({-1})
  for p in eq:
    sign_lookup[utils.hashable(p)] = \
        sign_lookup[utils.hashable(p)].intersection({0})
  for p in ne:
    sign_lookup[utils.hashable(p)] = \
        sign_lookup[utils.hashable(p)].intersection({-1, 1})

  return sign_lookup

class DiscDerSigns:

  def __init__(self, point):
    self.point = point
    self.neg_polies, self.zer_polies, self.pos_polies = [], [], []
    self.all_polies = []
    self.__lookup = {}
  
  def add_pos_poly(self, poly):
    self.pos_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[utils.hashable(poly)] = 1
    
  def add_neg_poly(self, poly):
    self.neg_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[utils.hashable(poly)] = -1
    
  def add_zer_poly(self, poly):
    self.zer_polies.append(poly)
    self.__add_poly_to_all_polies(poly)
    self.__lookup[utils.hashable(poly)] = 0
    
  def get_all_polies(self):
    return self.all_polies
    
  def set_origin_poly(self, poly):
    self.origin = poly
    
  def __add_poly_to_all_polies(self, poly):
    if poly in self.all_polies:
      raise "poly already there"
    self.all_polies.append(poly)
    
  def get_sign(self, poly):
    return self.__lookup[utils.hashable(poly)]
    
  def __repr__(self):
    #return '[\npoint: %s\n  <:%s\n  0:%s\n  >:%s\n]' \
    #    %(self.point, self.neg_polies, self.zer_polies, self.pos_polies)
    degrees = map(lambda p: len(p), self.get_all_polies())
    pos_degs = map(lambda p: len(p), self.pos_polies)
    neg_degs = map(lambda p: len(p), self.neg_polies)
    zer_degs = map(lambda p: len(p), self.zer_polies)

    pos_key, zer_key, neg_key = "", "", ""
    if degrees != []:
      for next_deg in range(len(self.origin), min(degrees), -1):
        deg = next_deg - 1
        pos_key += "1," if deg in pos_degs else "0,"
        neg_key += "1," if deg in neg_degs else "0,"
        zer_key += "1," if deg in zer_degs else "0,"
      pos_key = pos_key[:-1]

    return '[point: %9s [<%s =%s >%s]\n%s]' \
        %(self.point.decimal(), neg_key, 
          zer_key, pos_key, self.origin)
#    return '[point: %s [<%s, =%s, >%s]]' \
#        %(self.point.decimal(), len(self.neg_polies), 
#        len(self.zer_polies), len(self.pos_polies))
    

def get_roots_as_dds(poly):
  """Get discriminating derivatives sign assignments for all the roots of a
  given polynomial.
  
  Keyword arguments:
  poly -- polynomial whose roots are returned.

  return -- list of DiscDerSigns corresponding to roots of the polynomial.
  """

  roots = z3rcf.MkRoots(poly)
  dds = list(get_discri_der_signs(roots, poly))
  map(lambda r: r.set_origin_poly(poly), dds)
  return dds

def get_discri_der_signs(roots, poly):
  """Gets dicrimating derivative assignment on roots for poly.

  Keyword arguments:
  roots -- roots that are to be discriminated.
  poly -- polynomial whos derivatives are inspected.

  return -- list of DiscDerSign that discriminate all roots
  """

  if len(roots) == 0:
    return []
  if len(roots) == 1:
    return [DiscDerSigns(roots[0])]
  
  der = utils.der(poly)
  
  zero_roots, pos_roots, neg_roots = ([], [], [])
  for root in roots:
    der_value = utils.eval_poly(der, root)
    
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
  
  
  if not len(pos_roots) == 0:
    discDerSigns = get_discri_der_signs(pos_roots, der)
    if not len(pos_roots) == len(roots):
      map(lambda p: p.add_pos_poly(der), discDerSigns)
    ret +=  discDerSigns
    
  if not len(neg_roots) == 0:
    discDerSigns = get_discri_der_signs(neg_roots, der)
    if not len(neg_roots) == len(roots):
      map(lambda p: p.add_neg_poly(der), discDerSigns)
    ret +=  discDerSigns
  
  return ret

