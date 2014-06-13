import numpy as np
import uni_vts as uni
import isym
import operator
import functools
import itertools as it

def vts(pz, ps):
  pzc = isym.convert(pz)
  psc = map(isym.convert, ps)
  print "p: %s" %pzc
  print "qs: %s" %psc
  z_size = uni.tarski_query(pzc, [1])
  print "z_size: %s" %z_size
  if z_size == 0:
    raise Exception('ret empty set')

  Bis = {}
  Mis = {}
  signs_psi = {}
  ada_psi = {}

  for i in range(len(psc) - 1, -1, -1):
    print "i: %s" %i
    pi = psc[i]
    print "p%d: %s" %(i, pi)
    pi_signs = get_signs(pi, pzc, z_size)
    Bis[i] = [0,1,2][0:len(pi_signs)]
    Mis[i] = get_Mi(Bis[i],  pi_signs)
    
    print "p%d signs: %s" %(i, pi_signs)
    print "B%d: %s" %(i, Bis[i])
    print "M%d: \n%s" %(i, Mis[i])

    if i == len(psc) - 1:
      print "last"
      signs_psi[i] = map(lambda s: (s,), pi_signs)
      ada_psi[i] = map(lambda p: (p,), Bis[i])
      continue
    
    prev_ada = ada_psi[i + 1]
    prev_signs = signs_psi[i + 1]
    print "prev_ada: %s" %prev_ada
    print "prev_signs: %s" %prev_signs
    Bi_Ada_prev = reduce(operator.add, 
        map(lambda a: map(lambda t: (a,) + t, prev_ada), Bis[i]))
    print "Bi ada prev: %s" %Bi_Ada_prev

    pis = psc[i:]

    taqs = get_tarski_queries(pzc, pis, Bi_Ada_prev)
    taqs_mat = map(lambda x: [x], taqs)
    print taqs

    ada_M = get_ada_M(prev_signs, prev_ada)
    print "ada_M: \n%s" %ada_M
    print "Mis[i]: \n%s" %Mis[i]
    Mip = np.kron(ada_M, Mis[i])
    Mip = np.kron(Mis[i], ada_M)
    Mip_inv = np.linalg.inv(Mip)
    cur_counts = Mip_inv * taqs_mat
    print "Mip_inv: \n%s" %Mip_inv
    print "Mip: \n%s" %Mip
    print "cur_counts: %s" %cur_counts.transpose()
    cur_signs = get_cur_signs(pi_signs, prev_signs, cur_counts)
    signs_psi[i] = cur_signs
    print signs_psi
    get_cur_ada(pi_signs, Bis[i], cur_signs, prev_signs, prev_ada)

def get_cur_ada(pi_signs, ada_pi, cur_signs, prev_signs, prev_ada):
  print "cur ada"
  print "pi_signs: %s" %pi_signs
  print "ada_pi: %s" %ada_pi
  print "cur_signs: %s" %cur_signs
  print "prev_signs: %s" %prev_signs
  print "prev_ada: %s" %prev_ada
  counts = {}
  for prev_sign in prev_signs:
    counts[prev_sign] = []
  for cur_sign in cur_signs:
    counts[cur_sign[1:]].append(cur_sign)
  signs_2 = []
  signs_3 = []
  for prev_sign in prev_signs:
    if len(counts[prev_sign]) >= 2:
      signs_2.append(prev_sign)
  for prev_sign in prev_signs:
    if len(counts[prev_sign]) >= 3:
      signs_3.append(prev_sign)
  print "2: %s" %str(signs_2)
  print "3: %s" %str(signs_3)
  print prev_ada
  print get_ada_M(signs_2, prev_ada)

def get_cur_signs(pi_signs, prev_signs, cur_counts):
  #print "pi_signs: %s" %pi_signs
  #print "prev_signs: %s" %prev_signs
  #print cur_counts
  #print "getting cur"
  pi_len = len(pi_signs)
  ret = []
  for i,m in enumerate(cur_counts):
    pi_index = i/pi_len
    prev_index = i%pi_len
    #print "(%d, %d)" %(pi_index, prev_index)
    
    count = m.item(0)
    if count < 0 or (round(count) - count) > 0.01:
      raise Exception("bad count: %s" %count)
    if count < 0.5:
      continue
    #print "!"
    #print pi_signs[pi_index]
    #print prev_signs[prev_index]
    signs = (pi_signs[pi_index], ) + prev_signs[prev_index]
    #print "signs: %s" %str(signs)
    ret.append(signs)
  #print ret
  return ret

def get_ada_M(signs, powers):
  print "signs: %s" %signs
  print "powers: %s" %powers

  ret = []
  for power in powers:
    #print "power: %s" %str(power)
    pp = map(lambda sign: make_power_product(coef_power_fun, sign, power), signs)
    #print pp
    ret.append(map(functools.partial(reduce, operator.mul), pp))
  return np.matrix(ret)
  
def get_tarski_queries(pzc, pis, Bi_Ada_prev):
  taq_bases = functools.partial(make_power_product, poly_power_fun, pis)
  taq_pp = map(taq_bases, Bi_Ada_prev)
  
  taq_polies = map(functools.partial(reduce, uni.multiply), taq_pp)
  taqs = map(functools.partial(uni.tarski_query, pzc), taq_polies)
  return taqs

def get_signs(p, pz, taq_1):
  squared = uni.multiply(p, p)
  taq_p = uni.tarski_query(pz, p)
  taq_pp = uni.tarski_query(pz, squared)
  #base_matrix = np.matrix([[1,1,1],[0,1,-1],[0,1,1]])
  #print base_matrix
  #inverted_base = np.linalg.inv(base_matrix)
  inverted_base = np.matrix([[10, 0, -10], [0, 5, 5], [0, -5, 5]])
  taq_matrix = np.matrix([[taq_1], [taq_p],[taq_pp]])
  c_matrix = inverted_base * taq_matrix / 10
  signs = []

  if (c_matrix.item(0) >= 1):
    signs.append(0)
  if (c_matrix.item(1) >= 1):
    signs.append(1)
  if (c_matrix.item(2) >= 1):
    signs.append(-1)
  return signs

def get_Mi(B, signs):
  Mi = np.matrix( map(lambda b: map(lambda s: s**b, signs), B) )
  return Mi

def make_power_product(power_fun, bases, exponents):
  # print "bases: %s" %list(bases)
  # print "exponents: %s" %list(exponents)
  return map(lambda (b,p): power_fun(b,p), zip(bases, exponents))

def coef_power_fun(coef, power):
  return coef**power

def poly_power_fun(poly, power):
  # print "poly: %s" %poly
  # print "power: %s" %power
  if power == 0:
    return [1]
  if power == 1:
    return poly
  if power == 2:
    return uni.multiply(poly, poly)
  raise Exception("power shouldn't be > 2, was (%d)" %power)

