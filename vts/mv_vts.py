import numpy as np
import uni_vts as uni
import utils
import isym
import operator
import functools
import itertools as it
import prog_printer as pp

def vts(pz, ps):
  pp.reset()
  pzc = isym.convert(pz)
  psc = map(isym.convert, ps)
  print "p: %s" %pzc
  print "qs: %s" %psc
  z_size = uni.tarski_query(pzc, [1])
  print "z_size: %s" %z_size
  if z_size == 0:
    raise Exception('no roots for ' + str(pz))

  Bis = {}
  Mis = {}
  signs_psi = {}
  ada_psi = {}
  for i in range(len(psc) - 1, -1, -1):
    pp.inc()
    pp.p("i: %s" %i)

    pi = psc[i]
    pp.p("p%d: %s" %(i, pi))
    pi_signs = get_signs(pi, pzc, z_size)
    Bis[i] = [0,1,2][0:len(pi_signs)]
    Mis[i] = get_Mi(Bis[i],  pi_signs)
    
    pp.p("p%d signs: %s" %(i, pi_signs))
    pp.p("B%d: %s" %(i, Bis[i]))
    pp.p("M%d: \n%s" %(i, Mis[i]))

    if i == len(psc) - 1:
      pp.p("LAST")
      signs_psi[i] = map(lambda s: (s,), pi_signs)
      ada_psi[i] = tuple(map(lambda p: (p,), Bis[i]))
      continue
    
    prev_ada = ada_psi[i + 1]
    prev_signs = signs_psi[i + 1]
    pp.p("prev_ada: %s" %str(prev_ada))
    pp.p("prev_signs: %s" %prev_signs)

    # B_i \times Ada(\mathcal{P}_{i+1}, Z)
    Bi_Ada_prev = reduce(operator.add, 
        map(lambda a: map(lambda t: (a,) + t, prev_ada), Bis[i]))
    pp.p("Bi ada prev: %s" %Bi_Ada_prev)

    pis = psc[i:]
    pp.p("pis: %s" %pis)

    taqs = get_tarski_queries(pzc, pis, Bi_Ada_prev)
    taqs_mat = map(lambda x: [x], taqs)
    pp.p(taqs)

    M_ada_signs = get_M_ada_signs(prev_signs, prev_ada)

    pp.p("M%d_ada_signs: \n%s" %(i + 1, M_ada_signs))
    pp.p("M%d: \n%s" %(i, Mis[i]))

    # Mip = np.kron(M_ada_signs, Mis[i])
    Mip = np.kron(Mis[i], M_ada_signs)
    Mip_inv = np.linalg.inv(Mip)
    cur_counts = Mip_inv * taqs_mat
    pp.p("Mip: \n%s" %Mip)
    pp.p("Mip_inv: \n%s" %Mip_inv)
    pp.p("cur_counts:\n%s" %cur_counts.transpose())

    cur_signs = get_cur_signs(pi_signs, prev_signs, cur_counts)
    signs_psi[i] = cur_signs

    cur_ada = get_cur_ada(pi_signs, Bis[i], prev_signs, prev_ada, cur_signs)
    ada_psi[i] = cur_ada

    pp.p("cur_signs: %s" %cur_signs)
    pp.p("cur_ada: %s" %str(cur_ada))

def get_cur_ada(pi_signs, ada_pi, prev_signs, prev_ada, cur_signs):
  pp.inc()
  pp.p("======\nget_cur ada")
  pp.p("pi_signs: %s" %pi_signs)
  pp.p("ada_pi: %s" %ada_pi)
  pp.p("prev_signs: %s" %prev_signs)
  pp.p("prev_ada: %s" %str(prev_ada))
  pp.p("cur_signs: %s" %cur_signs)
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
  pp.p("2: %s" %str(signs_2))
  pp.p("3: %s" %str(signs_3))
  pp.p(prev_ada)
  r2_mat = get_M_ada_signs(signs_2, prev_ada)
  r3_mat = get_M_ada_signs(signs_3, prev_ada)
  a2_index = n_lin_indep_rows(r2_mat, len(signs_2))
  a3_index = n_lin_indep_rows(r3_mat, len(signs_3))
  part0 = make_sub_a(0, prev_ada, range(len(prev_ada)))
  part1 = make_sub_a(1, prev_ada, a2_index)
  part2 = make_sub_a(2, prev_ada, a3_index)
  pp.dec()
  return part0 + part1 + part2

def make_sub_a(prefix, prev_ada, selector):
  pp.p("prefix: %d" %prefix)
  pp.p("prev_ada: %s" %str(prev_ada))
  pp.p("selector: %s" %str(selector))
  return tuple((prefix,) + prev_ada[i] for i in selector)

def n_lin_indep_rows(mat, n):
  if n == 0:
    return ()
  f_rank = np.linalg.matrix_rank
  rows = (0,)
  rank = f_rank(mat[rows, ])
  if rank != 1:
    raise Exception("should be impossible to have zero row as first row")
  for index in range(1, len(mat)):
    # print "index: %d" %index
    temp_rows = rows + (index, )
    temp_rank = f_rank(mat[temp_rows,])
    # print "rank: %d" %rank
    # print "temp_rank: %d" %temp_rank
    # print "temp_rows: %s" %str(temp_rows)
    if temp_rank > rank:
      rows = temp_rows
      rank = temp_rank
  if rank != n:
    raise Exception("not enough rows")
  return rows

def get_cur_signs(pi_signs, prev_signs, cur_counts):
  pp.inc()
  #pp.p("pi_signs: %s" %pi_signs)
  #pp.p("prev_signs: %s" %prev_signs)
  # pp.p(cur_counts)
  
  prev_len = len(prev_signs)
  ret = []
  for i,m in enumerate(cur_counts):
    pi_index = i/prev_len
    prev_index = i%prev_len
    #pp.p("%d" %(i))
    #pp.p("(%d, %d)" %(pi_index, prev_index))
    
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

  pp.dec()
  return ret

def get_M_ada_signs(signs, powers):
  """Matrix where rows are raised to the powers. First row is first power,
  second row is second power etc

  """

  pp.inc()
  # pp.p("======\nget_M_ada_signs")
  # pp.p("signs: %s" %signs)
  # pp.p("powers: %s" %str(powers))
  ret = []
  for power in powers:
    #print "power: %s" %str(power)
    pow_prod = map(lambda sign: make_power_prod(coef_power_fun, sign, power), signs)
    #print pow_prod
    ret.append(map(functools.partial(reduce, operator.mul), pow_prod))

  pp.dec()
  return np.matrix(ret)
  
def get_tarski_queries(pzc, pis, Bi_Ada_prev):
  taq_bases = functools.partial(make_power_prod, poly_power_fun, pis)
  taq_pp = map(taq_bases, Bi_Ada_prev)
  
  taq_polies = map(functools.partial(reduce, utils.multiply), taq_pp)
  taqs = map(functools.partial(uni.tarski_query, pzc), taq_polies)
  return taqs

def get_signs(p, pz, taq_1):
  squared = utils.multiply(p, p)
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

def make_power_prod(power_fun, bases, exponents):
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
    return utils.multiply(poly, poly)
  raise Exception("power shouldn't be > 2, was (%d)" %power)

