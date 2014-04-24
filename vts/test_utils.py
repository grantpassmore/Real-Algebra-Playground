import unittest

import utils

class UtilsTest(unittest.TestCase):

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
      rem = utils.signed_prem(f, g)
#      print "f: %s" %f
#      print "g: %s" %g
#      print "rem: %s" %rem
#      print "exp: %s" %v
      self.assertEquals(v, rem)

if __name__ == '__main__':
  unittest.main()
