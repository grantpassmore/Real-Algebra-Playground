"""Module for Muchnik procedure (both for real and complex)"""

import sys
from collections import defaultdict

from blist import sortedset


class AlgebraAPIWrapper:
  """Wrapper which defines needed algebraic operations:
  leading term, leading coefficient, leading scalar [TODO remove], 
  degree, division, pseudo-division, tail of polynomial, has variables,
  derivative, sign of scalar [TODO remove]
  """
  def LT(self, p):
    self.__errMsg()
  def LC(self, p):
    self.__errMsg()
  #leading scalar
  def LS(self, p):
    self.__errMsg()
  def degree(self, p):
    self.__errMsg()
  def div(self, p, q):
    self.__errMsg()
  def p_tail(self, p):
    self.__errMsg()
  def e_var(self):
    self.__errMsg()
  def has_variable(self, p):
    self.__errMsg()
  def pseudo_div(p, q):
    self.__errMsg()
  def derivative(self, p):
    self.__errMsg()
  def zero(self):
    self.__errMsg()
  def sign(self, scalar):
    self.__errMsg()
  def __errMsg(self):
    raise Exception("method not implemented")


class Muchniker:
  """Form a Muchniker from algebra

  Keyword arguments:
  algebra -- implements AlgebraAPIWrapper
  """
  def __init__(self, algebra):
    """Construct Muchniker from algebra
    """
    self._algebra = algebra

  def c_assignment_all_one(self, const_frag):
    """Assignment for complex terms, where everything is assigned 1
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if c == 0:
        root_diagram[c][0] = (0, c)
      else:
        root_diagram[c][0] = (1, c)
    
    return root_diagram

  def c_assignment_all_zero(self, const_frag):
    """Assignment for complex terms, where everything is assigned 0
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if c == 0:
        root_diagram[c][0] = (0, c)
      elif self._algebra.has_variable(c):
        root_diagram[c][0] = (0, c)
      else:
        root_diagram[c][0] = (1, c)
    
    return root_diagram

  def _get_interactive_value(self, target, allowed):
    print "value for: %s: " %str(target),
    v = raw_input()
    if not(v in allowed):
      print "bad value - must be in %s" %allowed
      return self._get_interactive_value(target, allowed)
    return int(v)

  def c_assignment_interactive(self, const_frag):
    """Manual assignment for complex terms
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if c == 0:
        root_diagram[c][0] = (0, c)
      elif self._algebra.has_variable(c):
        v = self._get_interactive_value(c, ["0","1"])
        root_diagram[c][0] = (v, c)
      else:
        root_diagram[c][0] = (1, c)
    return root_diagram

  def _diagram_copy(self, diagram):
    # deep enough copy
    ret = defaultdict(dict)
    for i in diagram:
      ret[i] = diagram[i].copy()
    return ret

  def _c_full_assignment(self, diagrams, var_frag):
    """Assigns all possible values for complex terms
    """
    if(len(var_frag) == 0):
      return diagrams
    sys.stdout.write("\r# of diagrams: %d" %(len(diagrams)*2))
    sys.stdout.flush()

    c = var_frag[0]
    rest = var_frag[1:]
    acc = []
    #ordered by binary values
    for diagram in diagrams:
      self._diagram_copy(diagram)
      d1 = self._diagram_copy(diagram)
      d2 = self._diagram_copy(diagram)
      d1[c][0] = (0, c)
      d2[c][0] = (1, c)
      acc.append(d1)
      acc.append(d2)
    return self._c_full_assignment(acc, rest)

  def r_assignment_all_pos(self, const_frag):
    """Assignment for real terms, where everything is positive
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if self._algebra.has_variable(c):
        c_sign = 1
      else:
        c_sign = self._algebra.sign(c)
      root_diagram[c][0] = (c_sign, c)
      root_diagram[c][0.5] = (c_sign, c)
      root_diagram[c][1.0] = (c_sign, c)
    return root_diagram

  def r_assignment_all_zero(self, const_frag):
    """Assignment for real terms, where everything is zero
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if self._algebra.has_variable(c):
        c_sign = 0
      else:
        c_sign = self._algebra.sign(c)
      root_diagram[c][0] = (c_sign, c)
      root_diagram[c][0.5] = (c_sign, c)
      root_diagram[c][1.0] = (c_sign, c)
    return root_diagram

  def r_assignment_all_neq(self, const_frag):
    """Assignment for real terms, where everything is negative
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if self._algebra.has_variable(c):
        c_sign = -1
      else:
        c_sign = self._algebra.sign(c)
      root_diagram[c][0] = (c_sign, c)
      root_diagram[c][0.5] = (c_sign, c)
      root_diagram[c][1.0] = (c_sign, c)
    return root_diagram

  def r_assignment_interactive(self, const_frag):
    """Manual assignment for complex terms
    """
    root_diagram = defaultdict(dict)
    for c in const_frag:
      if self._algebra.has_variable(c):
        c_sign = self._get_interactive_value(c, ["-1", "0","1"])
      else:
        c_sign = self._algebra.sign(c)
      root_diagram[c][0] = (c_sign, c)
      root_diagram[c][0.5] = (c_sign, c)
      root_diagram[c][1.0] = (c_sign, c)
    return root_diagram    

  def _r_full_assignment(self, diagrams, var_frag):
    if(len(var_frag) == 0):
      return diagrams
    print len(diagrams)
    c = var_frag[0]
    rest = var_frag[1:]
    acc = []
    #ordered by binary values
    for diagram in diagrams:
      self._diagram_copy(diagram)
      d1 = self._diagram_copy(diagram)
      d2 = self._diagram_copy(diagram)
      d3 = self._diagram_copy(diagram)
      for point in [0, 0.5, 1.0]:
        d1[c][point] = (-1, c)
        d2[c][point] = (0, c)
        d3[c][point] = (1, c)
      acc.append(d1)
      acc.append(d2)
      acc.append(d3)
    return self._r_full_assignment(acc, rest)

  def muchnik_sequence(self, polies_done, polies_todo):
    """Calculates the Muchnik sequence for polynomials
    
    This function should be called as muchnik_sequence([], list)
    
    Keyword arguments:
    polies_done -- polynomials that have already been processed
    polies_todo -- polynomials that have not been processed yet
    """
    if(len(polies_done) % 2 == 0):
#      print "(%d, %d)" %(len(polies_done),len(polies_todo))
       sys.stdout.write("\r(polies done, polies to inspect): (%d, %d)" 
                        %(len(polies_done),len(polies_todo)))
       sys.stdout.flush()

    if len(polies_todo) == 0:
      print ""
      return polies_done

    head = polies_todo[0]
    rest = polies_todo[1:]

    #skip if already done
    if head in polies_done:
      return self.muchnik_sequence(polies_done, rest)

    #degree of the current polynomial
    cur_degree = self._algebra.degree(head)
    
    der = self._algebra.derivative(head)
    tail = self._algebra.p_tail(head)
    
    #expand by derivative and tail
    if tail != 0:
      rest.append(tail)
    if der != 0:
      rest.append(der)

    # could optimize (polys are sorted), but not need for this now, since
    # division is the bottleneck
    le = filter(
      (lambda p : 
        (self._algebra.degree(p) <= cur_degree) & 
        (self._algebra.degree(p) > 0)
      ), 
      polies_done
    )
    ge = filter(
      (lambda p : 
        (self._algebra.degree(p) >= cur_degree) & 
        (self._algebra.degree(p) > 0)
      ), 
      polies_done
    )

    # all remainders gotten by dividing p with lesser polies
    rem_le = map((lambda p: self._algebra.pseudo_div(head, p)[1]), le)
    # all remainders gotten by dividing p with greater polies
    rem_ge = map((lambda p: self._algebra.pseudo_div(p, head)[1]), ge)
    
    # filter zeros
    rems = filter(lambda p: p != 0, rem_le + rem_ge)

    #add all possible remainders
    polies_done.add(head)
    return self.muchnik_sequence(polies_done, rest + rems)

  def complex_extend(self, diagram, nonconst_frag):
    """Extends the unlabelled root diagram by polynomials
    
    Assumes that polynomials are ordered
    
    Keyword arguments:
    diagram -- unlabelled root diagram to be expanded
    nonconst_frag -- polynomials to be expanded by
    """
    if len(nonconst_frag) == 0:
      return diagram
  
    # polynomial under watch
    p = nonconst_frag[0]
    todo = nonconst_frag[1:]
    
    # add entry for anti-solution
    diagram[p][0] = (1, p)
  
    # if leading coefficient is zero then copy tail
    lc_row = self._algebra.LC(p) * fac(self._algebra.degree(p))
    if(diagram[lc_row][0][0] == 0):
      tail = self._algebra.p_tail(p)
      for col in diagram[tail].keys():
        diagram[p][col] = (diagram[tail][col][0], p)
      return self.complex_extend(diagram, todo)
  
    # variable which holds how many roots are already found
    roots_done = 0
    # number of columns
    colSize = len(diagram[self._algebra.zero()]) # corresponds to zero
  
    rest_polies = set(diagram.keys())
    rest_polies.remove(p)
  
    # 0 index is the anti-solution, rest are roots of something
    for col in range(1, colSize):
      # this should be removable
      # diagram[p][col] = (1, p)
      
      zeros = sortedset(key = self._poly_deg_key)
      # find the minimal degree polynomial
      for q in rest_polies:
        # only interested in non zero polies
        if((diagram[q][col][0] == 0) & (diagram[q][0][0] != 0)):
          zeros.add(q)
      
      # guaranteed to have at least one
      rem = self._algebra.pseudo_div(p, zeros[0])[1]
      value = diagram[rem][col][0]
      if(value == 0):
        roots_done += 1
        running_der = p
        
        # counts the multiplicity of the root
        for dp in range(self._algebra.degree(p)):
          running_der = self._algebra.derivative(running_der)
          if diagram[running_der][col][0] != 0:
            break
          roots_done += 1
          
      # add value to diagram
      diagram[p][col] = (value, p)
    
  
    # add new roots (thier multiplicity is always 1)
    for i in range(self._algebra.degree(p) - roots_done):
      column = colSize + i
      #iterate over other polynomials
      for q in rest_polies:
        # check if is zero column
        if diagram[q][0][0] == 0:
          diagram[q][column] = (0, q)
          continue
        diagram[q][column] = (1, q)
      diagram[p][column] = (0, p)
    return self.complex_extend(diagram, todo)

  def complex_partial(self, ps, assigner = c_assignment_interactive):
    """Partial Muchnik procedure over complexes
    
    Keyword arguments:
    ps -- input polynomials
    assigner -- assigner which determines to which terms are assigned.
                Either c_assignment_all_zero, c_assigment_all_one or
                c_assigment_interactive
    """
    muchnik_seq = self.muchnik_sequence(
      sortedset([self._algebra.zero()], key = self._poly_deg_key), ps)
    
    # constant fragment of the polynomials
    # (constant with respect to variable to be eliminated)
    constant_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] == 0, 
      muchnik_seq
    )
    # non-constant fragment of the polynomials
    nonconst_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] != 0, 
      muchnik_seq
    )

    root_diagram = assigner(constant_frag)
    
    diagram = self.complex_extend(root_diagram, nonconst_frag)
    
    self.pprint_diagram(diagram)

  def complex_full(self, equalities, inequalities):
    """Full Muchnik procedure over complexes
    
    Keyword arguments:
    equalities -- polynomials that are zero
    inequalities -- polynomials that are not zero
    
    return -- list of 2-tuples, each 2-tuple corresponds to assignments
    that satisfied the input parameters. Tuples consists of list of 
    polynomials that are: (== 0, == 0)
    """
    ps = equalities + inequalities
    
    muchnik_seq = self.muchnik_sequence(
      sortedset([self._algebra.zero()], key = self._poly_deg_key), ps)
      
    # constant fragment of the polynomials
    # (constant with respect to variable to be eliminated)
    constant_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] == 0, 
      muchnik_seq
    )
    # non-constant fragment of the polynomials
    nonconst_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] != 0, 
      muchnik_seq
    )

    # fragment with other variables that that which is to be eliminated
    var_frag = filter(
      lambda p: self._algebra.has_variable(p), 
      constant_frag
    )
    # fragment with only scalars
    sca_frag = filter(
      lambda p: not(self._algebra.has_variable(p)), 
      constant_frag
    )

    # gets the root diagram for scalars
    # (assigment type doesn't matter - nothing is assigned here)
    root_diagram = self.c_assignment_all_zero(sca_frag)
    
    # all possible assignments for variable fragments
    diagrams = self._c_full_assignment([root_diagram], var_frag)
    print ""
    progress = 0.0
    
    # extends all diagrams
    ext_diagrams = []
    for diagram in diagrams:
      extended = self.complex_extend(diagram, nonconst_frag)
      ext_diagrams.append(extended)
      #self.pprint_diagram(extended)
      progress = progress + 1
      sys.stdout.write("\rroot diagrams extended: %.2f%%" %
        (progress * 100 / len(diagrams)))
      sys.stdout.flush()
#      if len(ext_diagrams) > 10:
#        break
    print ""

    # determines whether diagrams satisfy the conditions
    good_diagrams = []
    for diagram in ext_diagrams:
      candidate_cols = diagram[self._algebra.zero()].keys()
      for equality_poly in equalities:
        still_good = []
        for col in candidate_cols:
          if diagram[equality_poly][col][0] == 0:
            still_good.append(col)
        candidate_cols = still_good
        if len(candidate_cols) == 0:
          break

      for inequality_poly in inequalities:
        still_good = []
        for col in candidate_cols:
          if diagram[inequality_poly][col][0] == 1:
            still_good.append(col)
        candidate_cols = still_good
        if len(candidate_cols) == 0:
          break

#      print "end_good: %s" %candidate_cols
      if len(candidate_cols) > 0:
        good_diagrams.append(diagram)

    # gathers the variable assignments
    ret = []
    for diagram in good_diagrams:
      self.pprint_diagram(diagram)
      zeros = []
      nonzeros = []
      for var_p in var_frag:
        if diagram[var_p][0][0] == 0:
          zeros.append(var_p)
        else:
          nonzeros.append(var_p)
      if (len(zeros + nonzeros) == 0):
        continue
      ret.append((zeros, nonzeros))
    
    self.pprint_clause(ret, {0:" == 0", 1:" != 0"})
    
    print "extended diagrams: %d" %len(ext_diagrams)
    print "good diagrams: %d" %len(good_diagrams)
    if len(good_diagrams) > 0:
      print "Satisfiable"
    else:
      print "Unsatisfiabl"
    return ret

  def real_extend(self, diagram, nonconst_frag):
    """Extends the sign diagram by polynomials
    
    Assumes that polynomials are ordered
    
    Keyword arguments:
    diagram -- sign to be expanded
    nonconst_frag -- polynomials to be expanded by
    """
    if len(nonconst_frag) == 0:
      return diagram
  
    #polynomial under watch
    p = nonconst_frag[0]
    deg_p = self._algebra.degree(p)
    todo = nonconst_frag[1:]
    rest_polies = set(diagram.keys())
  
    #if leading coefficient is zero then copy tail
    lc_row = self._algebra.LC(p) * fac(self._algebra.degree(p))
    if(diagram[lc_row][0][0] == 0):
      tail = self._algebra.p_tail(p)
      for col in diagram[tail].keys():
        diagram[p][col] = (diagram[tail][col][0], p)
      return self.real_extend(diagram, todo)
  
    #end values
    diagram[p][0] = (diagram[lc_row][0][0] * (-1)**deg_p, p)
    diagram[p][1.0] = (diagram[lc_row][1.0][0], p)
  
    zero_cols = sortedset(diagram[self._algebra.zero()].keys())
    zipped_cols = zip(zero_cols, range(len(zero_cols)))
  
    for col_ind in zipped_cols[1:-1]:
      zeros = sortedset(key = self._poly_deg_key)
      col = col_ind[0]
      ind = col_ind[1]
      #find the minimal degree polynomial
      for q in rest_polies:
        #only interested in non zero polies
        if((diagram[q][col][0] == 0) & (diagram[q][0][0] != 0)):
          zeros.add(q)
      if len(zeros) != 0:
        quot, rem = self._algebra.pseudo_div(p, zeros[0])
        #poly can be multiplied by a negative coef 
        #(resulting in a changed sign)
        #assumes this is always max power

        ps_coef = self._algebra.LC(zeros[0]) * \
          fac(self._algebra.degree(zeros[0]))
        ps_neg = diagram[ps_coef][col][0] < 0
        ps_deg = self._algebra.degree(p) - self._algebra.degree(zeros[0]) + 1
        ps_odd_deg = ps_deg % 2 == 1

        
        value = diagram[rem][col][0]
#        print "v: %s" %value
#        print "psc: %s" %ps_coef
#        print "ps_deg: %s" %ps_deg
#        print "odd: %s" %ps_odd_deg
#        print "neg: %s" %ps_neg

        # IMPORTANT! change the value if coef was negative
        if ps_neg & ps_odd_deg:
          value = -value 
#        print "v: %s" %value
        diagram[p][col] = (value, p)
    for col_ind in zipped_cols[1:-1]:
      zeros = sortedset(key = self._poly_deg_key)
      col = col_ind[0]
      ind = col_ind[1]
      #find the minimal degree polynomial
      for q in rest_polies:
        #only interested in non zero polies
        if((diagram[q][col][0] == 0) & (diagram[q][0][0] != 0)):
          zeros.add(q)
      if len(zeros) == 0:
        left_col = zipped_cols[ind-1][0]
        right_col = zipped_cols[ind+1][0]
        left_val = diagram[p][left_col][0]
        right_val = diagram[p][right_col][0]
        if (left_val,right_val) == (0, 0):
          raise DiagramExc("bad diagram, doesn't have derivative's root")
        else: #both are not zeros
          #equal and not zeros, or one of them is zero (both can't be)
          if (left_val == right_val) | (left_val * right_val == 0):
            value = self._algebra.sign(left_val + right_val)
            diagram[p][col] = (value, p)
          else: #opposite nonzero signs
            left_new_col = (col + left_col) / 2
            right_new_col = (col + right_col) / 2
            diagram[p][left_new_col] = (left_val, p)
            diagram[p][col] = (0, p)
            diagram[p][right_new_col] = (right_val, p)
            for q in rest_polies:
              diagram[q][left_new_col] = diagram[q][col]
              diagram[q][right_new_col] = diagram[q][col]
    return self.real_extend(diagram, todo)

  def real_partial(self, ps, assigner = r_assignment_interactive):
    """Partial Muchnik procedure over reals
    
    Keyword arguments:
    ps -- input polynomials
    assigner -- assigner which determines to which terms are assigned.
                Either r_assignment_all_pos, c_assigment_all_zero, 
                r_assignment_all_neg or r_assigment_interactive
    """
    muchnik_seq = self.muchnik_sequence(
      sortedset([self._algebra.zero()], key = self._poly_deg_key), 
      ps
    )

    constant_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] == 0, 
      muchnik_seq
    )
    nonconst_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] != 0, 
      muchnik_seq
    )

#    root_diagram = self.r_assignment_all_pos(constant_frag)
#    root_diagram = self.r_assignment_interactive(constant_frag)
    root_diagram = assigner(constant_frag)
    self.pprint_diagram(root_diagram)

    diagram = self.real_extend(root_diagram, nonconst_frag)

    #self.pprint_diagram(diagram)

  def real_full(self, lesser, equalities, greater):
    """Full Muchnik procedure over reals
    
    Prints out all the suitable extended diagrams
    
    Keyword arguments:
    lesser -- polynomials that are less than zero
    equalities -- polynomials that are zero
    greater -- polynomials that are greater than zero
    
    return -- list of 3-tuples, each 3-tuple corresponds to assignments
    that satisfied the input parameters. Tuples consists of list of 
    polynomials that are: ( < 0, == 0, > 0)
    """

    ps = lesser + equalities + greater
    muchnik_seq = self.muchnik_sequence(
      sortedset([self._algebra.zero()], key = self._poly_deg_key), 
      ps
    )
    
    constant_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] == 0, 
      muchnik_seq
    )
    nonconst_frag = filter(
      lambda p: self._algebra.div(p, self._algebra.e_var())[0] != 0, 
      muchnik_seq
    )

    var_frag = filter(lambda p: self._algebra.has_variable(p), constant_frag)
    sca_frag = filter(
      lambda p: not(self._algebra.has_variable(p)), constant_frag
    )

    root_diagram = self.r_assignment_all_zero(sca_frag)
#    self.pprint_diagram(root_diagram)
    
    diagrams = self._r_full_assignment([root_diagram], var_frag)

    # extends all diagrams
    progress = 0.0
    ext_diagrams = []
    for diagram in diagrams:
      progress = progress + 1
      #bad arises when [x-y, (x-1)**2]
      try:
        extended = self.real_extend(diagram, nonconst_frag)
        ext_diagrams.append(extended)
      except DiagramExc as ex:
#      except Exception as ex:
        print "==========\nBAD DIAGRAM\n%s\n==========" %ex
        self.pprint_diagram(diagram)
      sys.stdout.write("\r------ %f" %(progress * 100 / len(diagrams)))
      sys.stdout.flush()
      if len(ext_diagrams) > 40:
        break
    print

    # determines whether diagrams satisfy the conditions
    good_diagrams = []
    for diagram in ext_diagrams:
      candidate_cols = diagram[self._algebra.zero()].keys()
      # self.pprint_diagram(diagram)
      # print sortedset(candidate_cols)
      for equality_poly in equalities:
        still_good = []
        for col in candidate_cols:
          if diagram[equality_poly][col][0] == 0:
            still_good.append(col)
        candidate_cols = still_good
        if len(candidate_cols) == 0:
          break
      # print candidate_cols

      for lesser_poly in lesser:
        still_good = []
        for col in candidate_cols:
          if diagram[lesser_poly][col][0] == -1:
            still_good.append(col)
        candidate_cols = still_good
        if len(candidate_cols) == 0:
          break
      # print candidate_cols
      for greater_poly in greater:
        still_good = []
        for col in candidate_cols:
          if diagram[greater_poly][col][0] == 1:
            still_good.append(col)
        candidate_cols = still_good
        if len(candidate_cols) == 0:
          break
      # print candidate_cols

#      print "end_good: %s" %candidate_cols
      if len(candidate_cols) > 0:
        good_diagrams.append(diagram)

    # gathers the variable assignments
    ret = []
    for diagram in good_diagrams:
      self.pprint_diagram(diagram)
      zeros = []
      less_than_zeros = []
      more_than_zeros = []
      for var_p in var_frag:
        if diagram[var_p][0][0] == 0:
          zeros.append(var_p)
        elif diagram[var_p][0][0] == -1:
          less_than_zeros.append(var_p)
        else:
          more_than_zeros.append(var_p)
      if (len(zeros + less_than_zeros + more_than_zeros) == 0):
        continue
      ret.append((less_than_zeros, zeros, more_than_zeros))
    
    self.pprint_clause(ret, {0:" < 0", 1:" == 0", 2:" > 0"})
    print "extended diagrams: %d" %len(ext_diagrams)
    print "good diagrams: %d" %len(good_diagrams)
    if len(good_diagrams) > 0:
      print "Satisfiable"
    else:
      print "Unsatisfiabl"
    return ret

  def _poly_deg_key(self, p):
    """constructs the key the key corresponding to powers of x"""
    return self._poly_deg_key_helper(p, [], [])

  def _poly_deg_key_helper(self, p, degrees, coefs):
    deg = self._algebra.degree(p)
    if deg <= 0:
      degrees.append(0)
      coefs.append(self._algebra.LS(p))
      return (degrees + coefs)
    degrees.append(self._algebra.degree(p))
    coefs.append(self._algebra.LS(p))
    return self._poly_deg_key_helper(p - self._algebra.LT(p), degrees, coefs)

  def pprint_clause(self, data, lookup):
    """Pretty prints the data clause
    
    Keyword arguments:
    data -- list of tuples, where elements are lists of polynomials
    lookup -- mapping between polynomial index and string representing
    conditions (== 0, < 0, > 0, != 0)
    """
    if (len(data) == 0):
      print "No assigments"
      return
    disj = []
    for conjData in data:
      conj = []
      for index in lookup.keys():
        conj += map(lambda p: "%s%s" %(p, lookup[index]), conjData[index])
      conjStr = reduce(lambda l, r: l + " & " + ("\n  %s"%r), conj)
      disj.append("(\n  %s\n)" %conjStr)
    disjStr = reduce(lambda l, r: l + " | \n" + str(r), disj)
    print "ans:\n%s" %disjStr

  def pprint_diagram(self, diagram):
    """Pretty prints diagram"""
    max_len = sortedset(map(lambda s: len(str(s)), diagram.keys()))[-1]
    header = sortedset()
    for row in diagram.keys():
      header.update(diagram[row].keys())

    for row in sortedset(diagram.keys(), key = self._poly_deg_key):
      print str("%%%ds   " %max_len) %row,
  #     print "%s " %diagram[row],
  #     for index in diagram[row].keys():
  #       print "%2s " %diagram[row][index][0],
      for col in header:
        if col in diagram[row]:
          print "%2s" %diagram[row][col][0],
        else:
          print " *",
      print ""
    print ""

#factorial function, used only twice
fac = lambda n: 1 if n <= 0 else n * fac(n-1)


class DiagramExc(Exception):
  """Exception for invalid diagram"""
  def __init__(self, msg):
    self.msg = msg
  def __str__(self):
    return repr(self.msg)
