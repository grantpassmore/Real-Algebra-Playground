import unittest

import sympy
import pyparsing

import grf_parser as parser

class TestGRFParser(unittest.TestCase):
  """Class for testing the GRF parser
  """
  def setUp(self):
    self.x = sympy.var('x')
    self.y = sympy.var('y')
    
  def test_nat(self):
    data = {'1':'1', '345':'345'
    }
    for input in data:
      results = parser.nat.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_real(self):
    data = {'0.0':0, '24.14241':24.14241, '0.9':0.9,
    }
    for input in data:
      results = parser.real.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_int(self):
    data = {
      '0': 0, '1213':1213, '-1': -1, '2.': 2
    }
    for input in data:
      results = parser.int.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  #def test_int_not_real(self):
  #  self.assertRaises(pyparsing.ParseException, 
  #    lambda : parser.int.parseString('2.5'))
      
  def test_number(self):
    data = {
      '0': 0, '1213':1213, '-1': -1,
      '0.': 0, '12.13':12.13, '-1.': -1, '0.55': 0.55,
    }
    for input in data:
      results = parser.number.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
    
    data2 = {
      '0': sympy.Integer,
      '0.': sympy.Integer,
      '0.5': sympy.Float,
    }
    for input in data2:
      results = parser.number.parseString(input)
      self.assertIsInstance(results[0], data2[input])
      
  def test_variable(self):
    data = {'aba':'aba', 'x': 'x', 'x_': 'x_', '_': '_', 'A':'A',
      'x_123':'x_123'
    }
    for input in data:
      results = parser.variable.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], sympy.var(data[input]))
      
  def test_var_or_number(self):
    data = {'x': x, '1.':1}
    for input in data:
      results = parser.var_or_number.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_fn_add(self):
    data = {'(+ 0 x)': x, '(+ x 1)': 1 + x, 
      '(+ 1 2)':3, '(+ x y)': x + y
    }
    for input in data:
      results = parser.fn_add.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_fn_mult(self):
    data = {'(* 1 x)': x, '(* x 2)': 2*x, 
      '(* 1 2)':2, '(* x y)': x * y
    }
    for input in data:
      results = parser.fn_mult.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_fn_sub(self):
    data = {'(- 0 x)': -x, '(- x 2)': x - 2, 
      '(- 1 2)': -1, '(- x y)': x - y
    }
    for input in data:
      results = parser.fn_sub.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_fn_div(self):
    data = {'(/ 0 x)': 0, '(/ x 2)': x / 2, 
      '(/ 1 2)': 0.5, '(/ x y)': x / y
    }
    for input in data:
      results = parser.fn_div.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_fn_neg(self):
    data = {'(- 0)': 0, '(-x)': -x, 
      '(- 1)': -1
    }
    for input in data:
      results = parser.fn_neg.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_fn(self):
    data = {'(+ x y)': x + y, '(* x y)': x * y, 
      '(- x y)': x - y, '(/ x y)': x / y, 
      '(- x)': -x
    }
    for input in data:
      results = parser.fn.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_term(self):
    data = {'x': x, '2' : 2, '(* x y)': x * y, '(-x)': -x, '(-(- x))': x, 
      '(-(-(- x)))': -x, '( * x (+ 2 (- y)))': x * (2 - y)
      
    }
    for input in data:
      results = parser.term.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_rln_le(self):
    data = {'(<= x y)': sympy.Le(x, y),
      '(<= x (+ 3 2))': sympy.Le(x, 5),
      '(<= 2 3)': True, '(<= 3 2)': False,
      '(<= 2 2)': True,
    }
    for input in data:
      results = parser.rln_le.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_rln_lt(self):
    data = {'(< x y)': sympy.Lt(x, y),
      '(< x (+ 3 2))': sympy.Lt(x, 5),
      '(< 2 3)': True, '(< 3 2)': False,
      '(< 2 2)': False,
    }
    for input in data:
      results = parser.rln_lt.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_rln_eq(self):
    data = {'(= x y)': sympy.Eq(x, y),
      '(= x (+ 3 2))': sympy.Eq(x, 5),
      '(= 2 3)': False, '(= 3 2)': False,
      '(= 2 2)': True,
    }
    for input in data:
      results = parser.rln_eq.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_rln_neg(self):
    data = {'(!= x y)': sympy.Ne(x, y),
      '(!= x (+ 3 2))': sympy.Ne(x, 5),
      '(!= 2 3)': True, '(!= 3 2)': True,
      '(!= 2 2)': False,
    }
    for input in data:
      results = parser.rln_neg.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
  
  def test_rln_ge(self):
    data = {'(>= x y)': sympy.Ge(x, y),
      '(>= x (+ 3 2))': sympy.Ge(x, 5),
      '(>= 2 3)': False, '(>= 3 2)': True,
      '(>= 2 2)': True,
    }
    for input in data:
      results = parser.rln_ge.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_rln_gt(self):
    data = {'(> x y)': sympy.Gt(x, y),
      '(> x (+ 3 2))': sympy.Gt(x, 5),
      '(> 2 3)': False, '(> 3 2)': True,
      '(> 2 2)': False,
    }
    for input in data:
      results = parser.rln_gt.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_rln(self):
    data = {
      '(>= x y)': sympy.Ge(x, y), '(> x y)': sympy.Gt(x, y),
      '(= x y)': sympy.Eq(x, y), '(!= x y)': sympy.Ne(x, y),
      '(<= x y)': sympy.Le(x, y), '(< x y)': sympy.Lt(x, y),
    }
    for input in data:
      results = parser.rln.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_fml(self):
    data = {
      '(>= x y)': sympy.Ge(x, y), '(> x y)': sympy.Gt(x, y),
      '(= x y)': sympy.Eq(x, y), '(!= x y)': sympy.Ne(x, y),
      '(<= x y)': sympy.Le(x, y), '(< x y)': sympy.Lt(x, y),
    }
    for input in data:
      results = parser.fml.parseString(input)
      self.assertEquals(len(results), 1)
      self.assertEquals(results[0], data[input])
      
  def test_fmls(self):
    data = {
      '': [], '()': [],
      '(>= x y)': [sympy.Ge(x, y)],
      '(>= x y)': [sympy.Ge(x, y)],
      '(>= x y) (< x y)': [sympy.Ge(x, y), sympy.Lt(x, y)],
      '(>= 2 2) (< 2 2) (= 3 3)': [True, False, True],
    }
    for input in data:
      results = parser.fmls.parseString(input)
      self.assertEquals(results.asList(), data[input])
  
  def test_cmd_antecedent(self):
    data = {
      '(antecedent (< x y))': [sympy.Lt(x, y)],
      '(antecedent (< x y) (= x 7.5))': [sympy.Lt(x, y), sympy.Eq(x, 7.5)],
      '(antecedent (= 2 3) (< 3 (* 2 2)))': [False, True],
    }
    for input in data:
      results = parser.cmd_antecedent.parseString(input)
      self.assertEquals(results['antecedent']['fmls'].asList(), data[input])
  
  def test_cmd_succedent(self):
    data = {
      '(succedent (< x y))': [sympy.Lt(x, y)],
      '(succedent (< x y) (= x 7.5))': [sympy.Lt(x, y), sympy.Eq(x, 7.5)],
      '(succedent (= 2 3) (< 3 (* 2 2)))': [False, True],
    }
    for input in data:
      results = parser.cmd_succedent.parseString(input)
      self.assertEquals(results['succedent']['fmls'].asList(), data[input])
  
  def test_cmd(self):
    data = {
      '(sequent "nimi" (antecedent ) (succedent ))': ([], []),
      '(sequent "nimi" (antecedent (= x y)) (succedent ))': 
        ([sympy.Eq(x, y)], []),
      '(sequent "nimi" (antecedent ) (succedent (= x y)))': 
        ([], [sympy.Eq(x, y)]),
      '(sequent "nimi" (antecedent (= x (-(-x)))) (succedent (= x y)))': 
        ([True], [sympy.Eq(x, y)]),
    }
    for input in data:
      results = parser.cmd.parseString(input)
      expected_ante = data[input][0]
      expected_succ = data[input][1]
      self.assertEquals(results['antecedent']['fmls'].asList(), expected_ante)
      self.assertEquals(results['succedent']['fmls'].asList(), expected_succ)
      
if __name__ == '__main__':
  unittest.main()