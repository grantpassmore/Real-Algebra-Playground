import unittest

import sympy

import uni_vts
import isym


class VTSTest(unittest.TestCase):

  def setUp(self):
    self.x = sympy.var('x')
    pass

  def test_remainder(self):
    data = {
      # divide by constant
      (( 1, 1), ( 1,)):[],
      (( 1, 2), ( 1,)):[],
      (( 1, 1), (-1,)):[],
      ((-2, 1), (-1,)):[],
      (( 1, 1), (-2,)):[],
      (( 2, 2), (-2,)):[],
      # divide by variable
      (( 1, 1), (0, 1)):[ 1],
      ((-1, 2), (0, 1)):[-1],
      ((-2, 1), (0, 1)):[-2],
      (( 1, 1), (0,-1)):[ 1],
      ((-1, 2), (0,-1)):[-1],
      ((-2, 1), (0,-1)):[-2],
      (( 1, 1), (0,-2)):[ 2],
      ((-1, 2), (0,-2)):[-2],
      ((-2, 1), (0,-2)):[-4],
      #divide by ax + b
      (( 1, 1), ( 1, 1)):[  ],
      ((-1, 2), (-1, 1)):[ 1],
      ((-2, 1), (-4, 1)):[ 2],
      (( 1, 1), ( 1,-1)):[ 2],
      ((-1, 2), (-1,-1)):[-3],
      ((-2, 1), (-4,-1)):[-6],
      (( 1, 1), ( 1,-2)):[ 3],
      ((-1, 2), (-1,-2)):[-4],
      ((-2, 1), (-4,-2)):[-8],
      # more than one division
      ((1, 4, 6), (0, -2)): [4],
      # bigger
      ((1, 1), (2, 2, 2)): [1,1],
    }
    for k, v in data.iteritems():
      f = list(k[0])
      g = list(k[1])
      rem = uni_vts.signed_pseudo_remainder(f, g)
#      print "f: %s" %f
#      print "g: %s" %g
#      print "rem: %s" %rem
#      print "exp: %s" %v
      self.assertEquals(v, rem)

  def test_signed_remainder_sequence(self):
    p, q = [24, -50, 35, -10, 1], [-50, 170, -220, 134, -38, 4]
    sequence = uni_vts.signed_remainder_sequence(p, q)
    expected = [
      [24, -50, 35, -10, 1], 
      [-50, 170, -220, 134, -38, 4], 
      [-24, 50, -35, 10, -1], 
      [98, -174, 90, -14], 
      [-196, 272, -76], 
      [28224, -28224]
    ]
    self.assertEquals(expected, sequence)

  def test_signed_remainder_cauchy_index(self):
    data = {
      ((0, 1), ()): 0,
      ((1,), (1,)):0,
      ((0,1), (1,)): 1,
      ((0,-1), (1,)): -1,
      ((0,1), (-1,)): -1,
      ((0,-1), (-1,)): 1,
      ((1,1), (1,1)):0,
      ((1,1), (1,2)):-1,
      ((1,2), (1,1)):1, 
      ((1, 0, 1), (1,)): 0, 
      ((1, 0, 1), (0,1)): 0,
      ((-1, 0, 1), (1,)): 0, 
      ((-1, 0, 1), (0,1)): 2,
      ((-1, 0, 1), (-1,1)): 1,
    }
    for (p, q), expected in data.iteritems():
      actual = uni_vts.signed_remainder_cauchy_index(list(p), list(q))
#      print p
#      print q
#      print "actual: %s" %actual
      self.assertEquals(expected, actual)

  def test_tarski_query(self):
    data = {
      ((1,), (1,)): 0,
      ((1,), (0, 1)): 0,
      ((0,1), (1,)): 1,
      ((0,1), (1,1)): 1,
      ((0,1), (-1,1)): -1,
      ((0,1), (0,-1,1)): 0,
      ((0,1), (0,-1,1)): 0,
      ((-1,0,1), (1,)): 2,
      ((-1,0,1), (-1,)): -2,
      ((-1,0,1), (0,1)): 0,
      ((-1,0,1), (-1,1)): -1,
      ((-1,0,1), (1,1)): 1,
      ((-1,0,1), (-2,1)): -2,
      ((-1,0,1), (2,1)): 2,

    }
    for (p, q), expected in data.iteritems():
      actual = uni_vts.tarski_query(list(p), list(q))
      print "actual: %s" %actual
      self.assertEquals(expected, actual)

if __name__ == '__main__':
  unittest.main()
