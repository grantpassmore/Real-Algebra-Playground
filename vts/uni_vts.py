import z3rcf
import sympy

class ConditionExc(Exception):
  def __init__(self, root, poly, value):
    self.root = root
    self.poly = poly
    self.value = value
  def __str__(self):
    print "root: %s" %self.root
    print "poly: %s" %self.poly
    return repr(self.value)


def internal_ts(eq, lt):
  for equality in eq:
    roots = z3rcf.MkRoots(equality)
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
  
def internal_vts(eq, lt):
  for equality in eq:
    roots = z3rcf.MkRoots(equality)
    for root in roots:
      try:
        evaluate_vts_root(root, eq, lt)
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

class EvalStr:
  def __init__(self, condition, msg):
    self.condition = condition
    self.msg = msg

__eq_str = EvalStr(lambda p: p == 0, 'Not equal to zero')
__lt_str = EvalStr(lambda p: p < 0, 'Not less than zero')

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
def evaluate_vts_root(root, eq, lt):
  print "evaling root: %s" % root
