import z3rcf
import utils

class ConditionExc(Exception):
  def __init__(self, root, poly, value):
    self.root = root
    self.poly = poly
    self.value = value
  def __str__(self):
    #print "root: %s" %self.root
    #print "poly: %s" %self.poly
    return repr(self.value)

def internal_ts(le, lt, eq, ne):
  """Determines the satisfiability of constraints by calculating polynomials on 
  points on all possible (solutions set) intervals
  
  Keyword arguments:
  le -- list of polynomial coefficients that are <= 0 (z3rcf format)
  lt -- list of polynomial coefficients that are < 0 (z3rcf format)
  eq -- list of polynomial coefficients that are = 0 (z3rcf format)
  ne -- list of polynomial coefficients that are != 0 (z3rcf format)
  
  return -- boolean corresponding to satisfiability of constraints
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
    return False
  

class EvalStr:
  def __init__(self, condition, msg):
    self.condition = condition
    self.msg = msg

__eq_str = EvalStr(lambda p: p == 0, 'Not equal to zero')
__lt_str = EvalStr(lambda p: p < 0, 'Not less than zero')
__le_str = EvalStr(lambda p: p <= 0, 'Not less or equal to zero')
__ne_str = EvalStr(lambda p: p != 0, 'Equal to zero')

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
    sum = utils.eval_poly(poly, point)
    #print "  term values: %s" %map(lambda (c, p): c*point**p, terms)
    #print "  sum: %s" %sum
    if not strategy.condition(sum):
      raise ConditionExc(point, poly, strategy.msg)
