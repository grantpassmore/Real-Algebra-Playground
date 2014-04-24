import unittest

import sympy
import z3rcf

import uni_vts
import isym


class VTSTest(unittest.TestCase):

  def setUp(self):
    self.x = sympy.var('x')
    def make_dds(p):
      rs = z3rcf.MkRoots(p)
      dds = uni_vts.get_discri_der_signs(rs, p)
      map(lambda d: d.set_origin_poly(p), dds)
      return sorted(dds, key=lambda p: p.point)
    self.make_dds = make_dds

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
    
  def test_pick_sign_of_goal(self):
    a, b, c = sympy.var('a'), sympy.var('b'), sympy.var('c')
    p1 = [a]
    p2 = [b]
    goal = [c]

    # shifts 0, 1, -1
    
    matrix = {k: 0 for k in range(27)}

    # p1 = 0, p2 = 0, goal > 0
    matrix[9*0 + 3*0 + 1] = 1
    dds = uni_vts.DiscDerSigns(0)
    dds.add_zer_poly(p1)
    dds.add_zer_poly(p2)
    goal_sign = uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix)
    self.assertEquals(1, goal_sign)
    matrix[1] = 0

    # p1 = 0, p2 = 0, goal < 0
    matrix[9*0 + 3* 0 + 2] = 1
    dds = uni_vts.DiscDerSigns(0)
    dds.add_zer_poly(p1)
    dds.add_zer_poly(p2)
    goal_sign = uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix)
    self.assertEquals(-1, goal_sign)
    matrix[2] = 0

    # p < 0, p2 > 0, goal = 0
    matrix[9*2 + 3*1 + 0] = 1
    dds = uni_vts.DiscDerSigns(0)
    dds.add_neg_poly(p1)
    dds.add_pos_poly(p2)
    goal_sign = uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix)
    self.assertEquals(0, goal_sign)
    
    # 21 = 22 = 1
    matrix[22] = 1
    self.assertRaises(Exception, 
        lambda: uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix))
    matrix[22] = 0

    # nothing is zero
    matrix[21] = 0
    self.assertRaises(Exception, 
        lambda: uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix))

    
    matrix[21] = 2
    self.assertRaises(Exception, 
        lambda: uni_vts.pick_sign_of_goal([p1, p2, goal], dds, matrix))
    
  def test_evaluate_single_on_sign_assignment(self):
    r1_poly = [-1, 0, 1]
    dds1 = self.make_dds(r1_poly)

    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1.1, 1]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [0.9, 1]))

    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[1], [-0.9, 1]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[1], [-1, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[1], [-1.1, 1]))
    
    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1, 0, 1]))
    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1, 0, 1]))
    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1, 0, 1]))

    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds1[0], [1, 0, 1]))

    # (x - 1)**2 * x * (x + 1) * (x + 2)
    r2_poly = [0, 2, -1, -3, 1, 1]
    dds2 = self.make_dds(r2_poly)
    
    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[0], [21, 10]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[0], [2, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[0], [19, 10]))

    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[1], [11, 10]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[1], [1, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[1], [9, 10]))

    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[2], [1, 10]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[2], [0, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[2], [-1, 10]))

    # NOTE double breaks down here
    t = sympy.S(9) / 10
    self.assertEquals(1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[3], [-1 + t, 1]))
    self.assertEquals(0, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[3], [-1, 1]))
    self.assertEquals(-1, 
        uni_vts.evaluate_single_on_sign_assignment(dds2[3], [-1 - t, 1]))

  def test_e_close_evaluate_single_on_sign_assignment(self):
    r1_poly = [-1, 0, 1]
    dds1 = self.make_dds(r1_poly)
    
    data = {
      (-1, 1): 1,
      (1, -1): -1,
      (-2, 1): -1,
      (0, 1): 1,
      (1, -2, 1): 1,
      (-1, 2, -1): -1,
    }
    for p, expected_sign in data.iteritems():
      actual = uni_vts.e_close_evaluate_single_on_sign_assignment(
          dds1[1], list(p))
      # print "p: %s" %list(p)
      # print "actual: %d" %actual
      self.assertEquals(expected_sign, actual)

  def test_sign_conditions_lookup(self):
    p1, p2, p3, p4 = map(lambda x: [sympy.var(x)] ,["p1", "p2", "p3", "p4"])

    sign_lookup = uni_vts.sign_conditions_lookup([p1], [p2], [p3], [p4])
    self.assertEquals({0, -1}, sign_lookup[uni_vts.make_poly_hashabel(p1)])
    self.assertEquals({-1}, sign_lookup[uni_vts.make_poly_hashabel(p2)])
    self.assertEquals({0}, sign_lookup[uni_vts.make_poly_hashabel(p3)])
    self.assertEquals({-1, 1}, sign_lookup[uni_vts.make_poly_hashabel(p4)])

    sign_lookup = uni_vts.sign_conditions_lookup([], [p1, p2], [], [])
    self.assertEquals({-1}, sign_lookup[uni_vts.make_poly_hashabel(p1)])
    self.assertEquals({-1}, sign_lookup[uni_vts.make_poly_hashabel(p2)])

    sign_lookup = uni_vts.sign_conditions_lookup([], [], [p1, p2], [])
    self.assertEquals({0}, sign_lookup[uni_vts.make_poly_hashabel(p1)])
    self.assertEquals({0}, sign_lookup[uni_vts.make_poly_hashabel(p2)])

    sign_lookup = uni_vts.sign_conditions_lookup([], [], [], [p1, p2])
    self.assertEquals({-1, 1}, sign_lookup[uni_vts.make_poly_hashabel(p1)])
    self.assertEquals({-1, 1}, sign_lookup[uni_vts.make_poly_hashabel(p2)])

    sign_lookup = uni_vts.sign_conditions_lookup([p1, p2], [], [], [])
    self.assertEquals({0, -1}, sign_lookup[uni_vts.make_poly_hashabel(p1)])
    self.assertEquals({0, -1}, sign_lookup[uni_vts.make_poly_hashabel(p2)])

  def test_vts(self):
    lin_1 = [-1, 1]
    lin_2 = [-2, 1]
    cub_1 = [-1, 3, -3, 1]
    qua_  = [1, 0, 1]

    self.assertEquals(True, 
                      uni_vts.internal_vts([lin_1], [], [lin_1], []))
    self.assertEquals(True, 
                      uni_vts.internal_vts([lin_1], [lin_1], [], []))
    self.assertEquals(False, 
                      uni_vts.internal_vts([], [], [lin_1], [lin_1]))
    self.assertEquals(False, 
                      uni_vts.internal_vts([], [], [lin_1, lin_2], []))
    self.assertEquals(True, 
                      uni_vts.internal_vts([], [], [lin_1], [lin_2]))

    self.assertEquals(True,
                      uni_vts.internal_vts([], [], [cub_1], []))
    self.assertEquals(True,
                      uni_vts.internal_vts([], [], [cub_1, lin_1], []))
    self.assertEquals(False,
                      uni_vts.internal_vts([], [], [cub_1], [lin_1]))

    self.assertEquals(False,
                      uni_vts.internal_vts([qua_], [], [], []))
    self.assertEquals(False,
                      uni_vts.internal_vts([], [qua_], [], []))
    self.assertEquals(False,
                      uni_vts.internal_vts([], [], [qua_], []))
    self.assertEquals(True,
                      uni_vts.internal_vts([], [], [], [qua_]))

    
if __name__ == '__main__':
  unittest.main()










