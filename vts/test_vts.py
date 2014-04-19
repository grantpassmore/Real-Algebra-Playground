import unittest

import sympy
import z3rcf

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
      # print "actual: %s" %actual
      self.assertEquals(expected, actual)

  def test_make_product_list(self):
    a0, a1 = map(sympy.var, ["a0", "a1"])

    data = {
      () : [[1]],
      ((a0, a1),):[[1], [a0,a1], [a0**2, 2*a0*a1, a1**2]]
    }
    
    for k, expected in data.iteritems():
      polies = map(list, k)
      actual = uni_vts.make_product_list(list(k))
#      print "actual: %s" %actual

      self.assertEqual(expected, actual)



  def test_make_product_list_longer(self):
    a0, a1, b0, b1, b2  = map(sympy.var, ["a0", "a1", "b0", "b1", "b2"])

    polies = [[a0, a1], [b0, b1, b2]]
    
    actual = uni_vts.make_product_list(polies)
    mps = map(lambda p: isym.convert_back(p).expand(), actual)

    sps = map(isym.convert_back, polies)

    pow_f = lambda  i, j: (sps[0]**i * sps[1]**j).expand()
    
    self.assertEquals(pow_f(0, 0), mps[0])
    self.assertEquals(pow_f(0, 1), mps[1])
    self.assertEquals(pow_f(0, 2), mps[2])

    self.assertEquals(pow_f(1, 0), mps[3])
    self.assertEquals(pow_f(1, 1), mps[4])
    self.assertEquals(pow_f(1, 2), mps[5])

    self.assertEquals(pow_f(2, 0), mps[6])
    self.assertEquals(pow_f(2, 1), mps[7])
    self.assertEquals(pow_f(2, 2), mps[8])

#    get_coefs = lambda p: map(
#      lambda i: sympy.div(p, x**i, x)[0].leadterm(x)[0], 
#      range(10)
#    )

  def test_get_discri_der_signs(self):
    print 
    # (x - 1)**2 * x * (x + 1) * (x + 2)
    poly = [0, 2, -1, -3, 1, 1]
    poly_1st_der = [2, -2, -9, 4, 5]
    poly_2nd_def = [-2, -18, 12, 20]
    poly_3rd_der = [-18, 24, 60]

    roots = z3rcf.MkRoots(poly)
    droots = uni_vts.get_discri_der_signs(roots, poly)

    # TODO change implementation first
    for discDerSign in droots:
      discDerSign.origin = poly
    for discDerSign in droots:
      self.assertEquals(poly, discDerSign.origin)
    sorted_roots =  sorted(droots, key = lambda p: p.point)
    neg_2 = sorted_roots[0]
    neg_1 = sorted_roots[1]
    zero = sorted_roots[2]
    pos_1 = sorted_roots[3]

    self.assertEquals(-2, neg_2.point)
    self.assertEquals(-1, neg_1.point)
    self.assertEquals(0, zero.point)
    self.assertEquals(1, pos_1.point)

#    print "zero : %s" %zero
#    print "neg_1: %s" %neg_1
#    print "neg_2: %s" %neg_2
    
    self.assertEquals([], neg_2.neg_polies)
    self.assertEquals([], neg_2.zer_polies)
    self.assertEquals([poly_3rd_der, poly_1st_der], neg_2.pos_polies)

    self.assertEquals([poly_1st_der], neg_1.neg_polies)
    self.assertEquals([], neg_1.zer_polies)
    self.assertEquals([], neg_1.pos_polies)
    
    self.assertEquals([poly_3rd_der], zero.neg_polies)
    self.assertEquals([], zero.zer_polies)
    self.assertEquals([poly_1st_der], zero.pos_polies)


    self.assertEquals([], pos_1.neg_polies)
    self.assertEquals([poly_1st_der], pos_1.zer_polies)
    self.assertEquals([], pos_1.pos_polies)
    
    

if __name__ == '__main__':
  unittest.main()
