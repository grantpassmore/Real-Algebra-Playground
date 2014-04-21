import unittest

import sympy

import isym

class TestIsym(unittest.TestCase):

  def setUp(self):
    self.x = sympy.var('x')

  def test_convert(self):
    data = {0: [], 1: [1], -2: [-2], 
      x: [0, 1], x - 7: [-7, 1], 3*x**2: [0, 0, 3],
      1 + x/3 - x**2/5: [15, 5, - 3],
    }
    poly = x**6 - 7*x**4 - x**3 - 1
    for poly, expected in data.iteritems():
      actual = isym.convert(poly)
      self.assertEquals(expected, actual)
      self.assertTrue( all( map(lambda p: type(p) == int, actual) ) )


  def test_convert_rationals_to_ints(self):
    q = lambda n, d: sympy.Rational(n, d)
    
    data = {
        (q(1,1), q(2,1)): [int, int],
        (1, sympy.Float(2.2)): [int, sympy.Float]
    }
    for coef_list, expected in data.iteritems():
      converted = isym.convert_rationals_to_ints(list(coef_list))
      actual = map(type, converted)
#      print "actual: %s" %actual
      self.assertEquals(expected, actual)


  def test_convert_back(self):
    data = {(): 0, (1,): 1, (-2,): -2,
      (0,1):x, (-7, 1): x - 7, (0, 0, 3): 3*x**2,
    }
    for lpoly, expected in data.iteritems():
      actual = isym.convert_back(lpoly)
      self.assertEquals(expected, actual)


if __name__ == '__main__':
  unittest.main()
