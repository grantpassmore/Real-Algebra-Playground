import pyparsing as pyp
import sympy
  
def doReal(s,l,t):
  if t[0] == "-":
    return -sympy.Float(t[1])
  else:
    return sympy.Float(t[0])

def doInt(s,l,t):
  if t[0] == "-":
    return -sympy.Integer(t[1])
  else:
    return sympy.Integer(t[0])

    
def doVariable(s, l, t):
  return sympy.var(t[0])
  #return sympy.var('x')
  
def proc_le(s, l, t):
  return sympy.Le(t[0], t[1])
def proc_lt(s, l, t):
  return sympy.Lt(t[0], t[1])
def proc_eq(s, l, t):
  return sympy.Eq(t[0], t[1])
def proc_neg(s, l, t):
  return sympy.Ne(t[0], t[1])
def proc_ge(s, l, t):
  return sympy.Ge(t[0], t[1])
def proc_gt(s, l, t):
  return sympy.Gt(t[0], t[1])

str_sym = pyp.QuotedString(quoteChar = '"', multiline=True)

nat = pyp.Word(pyp.nums)

lit_dot = pyp.Literal(".")
lit_unary_neg = pyp.Literal('-')

int = (pyp.Optional(lit_unary_neg) + nat + pyp.Optional(lit_dot)).\
  setParseAction(doInt)

real = (pyp.Optional(lit_unary_neg) + 
    pyp.Combine(nat + lit_dot + nat)).\
  setParseAction(doReal)


# can't parse 1. as sympy.Float(1)
# sympy.var('x') != sympy.var('x') * sympy.Float(1)
# sympy.var('x') == sympy.var('x') * sympy.Integer(1)  
# TODO make nat.nat not int (2)
number = (real | int)

lit_lpar = pyp.Literal('(').suppress()
lit_rpar = pyp.Literal(')').suppress()

lit_sequent = pyp.Literal('sequent')
lit_antecedent = pyp.Literal('antecedent')
lit_succedent = pyp.Literal('succedent')

variable = pyp.Word(pyp.alphas + '_', pyp.alphanums + '_').\
  setParseAction(doVariable)#('var')

var_or_number = (number | variable)

lit_plus = pyp.Literal('+').suppress()
lit_times = pyp.Literal('*').suppress()
lit_minus = lit_unary_neg.suppress()
lit_div = pyp.Literal('/').suppress()

term = pyp.Forward()

fn_add = (lit_lpar + lit_plus + term + term + lit_rpar).\
  setParseAction(lambda s, l, t: t[0] + t[1])
fn_mult = (lit_lpar + lit_times + term + term + lit_rpar).\
  setParseAction(lambda s, l, t: t[0] * t[1])
fn_sub = (lit_lpar + lit_minus + term + term + lit_rpar).\
  setParseAction(lambda s, l, t: t[0] - t[1])
fn_div = (lit_lpar + lit_div + term + term + lit_rpar).\
  setParseAction(lambda s, l, t: t[0] / t[1])
fn_neg = (lit_lpar + lit_minus + term + lit_rpar).\
  setParseAction(lambda s, l, t: -t[0])
  

fn = (fn_add | fn_mult | fn_sub | fn_div | fn_neg)#.setParseAction(lambda s, l, t: t[0].expand())
term << (var_or_number | fn)

kw_le = pyp.Keyword('<=').suppress()
kw_lt = pyp.Keyword('<').suppress()
kw_eq = pyp.Keyword('=').suppress()
kw_neg = pyp.Keyword('!=').suppress()
kw_ge = pyp.Keyword('>=').suppress()
kw_gt = pyp.Keyword('>').suppress()

rln_le = (lit_lpar + kw_le + term + term + lit_rpar).\
  setParseAction(proc_le)
rln_lt = (lit_lpar + kw_lt + term + term + lit_rpar).\
  setParseAction(proc_lt)
rln_eq = (lit_lpar + kw_eq + term + term + lit_rpar).\
  setParseAction(proc_eq)
rln_neg = (lit_lpar + kw_neg + term + term + lit_rpar).\
  setParseAction(proc_neg)
rln_ge = (lit_lpar + kw_ge + term + term + lit_rpar).\
  setParseAction(proc_ge)
rln_gt = (lit_lpar + kw_gt + term + term + lit_rpar).\
  setParseAction(proc_gt)
  
rln = rln_le | rln_lt | rln_eq | rln_neg | rln_ge | rln_gt

fml = pyp.Forward()

fml << ( rln )
fmls = pyp.ZeroOrMore(fml)

cmd_antecedent = (lit_lpar + lit_antecedent + pyp.Group(fmls)('fmls') + lit_rpar)\
  ('antecedent') 
cmd_succedent = (lit_lpar + lit_succedent + pyp.Group(fmls)('fmls') + lit_rpar)\
  ('succedent')
cmd = (lit_lpar + lit_sequent + str_sym('str_name') + cmd_antecedent + cmd_succedent + lit_rpar)
  

      