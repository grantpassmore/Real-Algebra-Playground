import unittest

import sympy

import isym

class TestIsym(unittest.TestCase):

  def setUp(self):
    self.x = sympy.var('x')
  def test_convert(self):
    data = {0: [], 1: [1], -2: [-2], 
      x: [0, 1], x - 7: [-7, 1], 3*x**2: [0, 0, 3],
    }
    poly = x**6 - 7*x**4 - x**3 - 1
    for poly, expected in data.iteritems():
      actual = isym.convert(poly)
      self.assertEquals(expected, actual)
      self.assertTrue( all( map(lambda p: type(p) == int, actual) ) )

    #check not int type
    self.assertEquals(type(isym.convert(sympy.S(1.5))[0]), type(sympy.S(1.5)))

    longer = isym.convert(sympy.S(2.5)*x + sympy.S(1))
    
    self.assertEquals(type(longer[1]), type(sympy.S(2.5)))
    self.assertEquals(type(longer[0]), type(sympy.S(1)))


  def test_convert_back(self):
    data = {(): 0, (1,): 1, (-2,): -2,
      (0,1):x, (-7, 1): x - 7, (0, 0, 3): 3*x**2,
    }
    for lpoly, expected in data.iteritems():
      actual = isym.convert_back(lpoly)
      self.assertEquals(expected, actual)


if __name__ == '__main__':
  unittest.main()
