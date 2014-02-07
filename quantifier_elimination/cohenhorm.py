from fractions import Fraction
import sys

from blist import sortedset


class CohenHormander:
  BOTTOM = -1

  def __init__(self, algebra):
    self._algebra = algebra

  def real_full(self, lesser, equalities, greater):
    """Cohen-Hormander procedure over reals
    
    Prints out all the suitable extended diagrams
    
    Keyword arguments:
    lesser -- polynomials that are less than zero
    equalities -- polynomials that are zero
    greater -- polynomials that are greater than zero
    
    return -- list of 3-tuples, each 3-tuple corresponds to assignments
    that satisfied the input parameters. Tuples consists of list of 
    polynomials that are: ( < 0, == 0, > 0)
    """
    polys = lesser + equalities + greater
    contexted_tables = self._real_table(polys, {})
    print
    
    # determine which whether diagrams satisify input conditions
    conditions = [(lesser, -1), (equalities, 0), (greater, 1)]
    good_tables = []
    for table, c in contexted_tables:
      # all columns are possible good
      candidate_cols = table[table.keys()[0]].keys()
      
      for (polies, cond) in conditions:
        # filter out columns that are invalid
        for poly in polies:
          still_good = []
          for col in candidate_cols:
            if table[poly][col] == cond:
              still_good.append(col)
          candidate_cols = still_good
          if len(candidate_cols) == 0:
            break
      
      if len(candidate_cols) > 0:
        good_tables.append((table, c))
    print "\n\nSUITABLE TABLES:\n"
    
    # construct the return value
    ret = []
    for table, c in good_tables:
      print "context: %s" %c
      self.pprint_diagram(table)
      le_assign = filter(lambda p: c[p] == -1, c.keys())
      eq_assign = filter(lambda p: c[p] == 0, c.keys())
      ge_assign = filter(lambda p: c[p] == 1, c.keys())
      ret.append((le_assign, eq_assign, ge_assign))
    
    return ret

  def _real_table(self, polys, context):
    """Constructs a diagram for polynomials using
    given context
    
    Keyword arguments:
    polys -- polynomials that are rows in the table
    context -- dictionary that associates  constants (with respect to
    the variable to be eliminated) with their sign (-1, 0, 1)
    
    return -- tuple of sign diagram and context
    """
    if len(polys) == 0:
      return {}
      
    # sort polynomials by their degrees  
    set = sortedset(polys, key = lambda p: - self._algebra.degree(p))
    # pick the next polynomial (which is of maximum degree)
    max_poly = set.pop(0)
    
    sys.stdout.write("\rdeg of max_poly: %d" %(self._algebra.degree(max_poly)))
    sys.stdout.flush()
    
    derivative = self._algebra.derivative(max_poly)

    # polynomials needed (all other + plus derivative)
    needed_polies = set.copy()
    # no need to add derivative when it's zero
    if (self._algebra.zero() != derivative):
      needed_polies.add(derivative)
      
    # means that max_poly is at most first degree polynomial and
    # therefore can be determined
    if len(needed_polies) == 0:
      contexted_tables = self.get_initial_table(max_poly, context)
      return contexted_tables
      
    # all the possible assignments that determine the leading
    # coefficient of needed polynomials
    # [context, [pol], mapping]
    exp_contexts = self.expand_context(context, needed_polies, {})
    
            
    ret = []
    for (con, pols, mpg) in exp_contexts:
      # calculate division when not constant
      # when constant remainder is zero
      # filters also zero polynomial out
      rems = map(
        lambda g: self._algebra.pseudo_div(max_poly, g)[1], 
        filter(lambda g: self._algebra.degree(g) > 0, pols)
      )
      # need diagram for listed polynomials and remainders
      new_goal = filter(
        lambda p: self._algebra.degree(p) >= 0, 
        pols + rems
      )
      
      # get all tables (list of tables and contexts)
      needed_tables = self._real_table(new_goal, con)

      # special case for when the max_poly has a undefined leading sign
      # by this point
      temp_needed = []
      max_poly_lc = self._algebra.LC(max_poly)
      if (self._algebra.degree(max_poly) == 0) & \
          self._algebra.has_variable(max_poly_lc):
        for (needed_table, table_con) in needed_tables:
          if table_con.has_key(max_poly_lc):
            temp_needed.append((needed_table, table_con))
            continue
          c1 = table_con.copy()
          c2 = table_con.copy()
          c3 = table_con.copy()
          c1[max_poly_lc] = -1
          c2[max_poly_lc] = 0
          c3[max_poly_lc] = 1
          temp_needed.append((needed_table, c1))
          temp_needed.append((needed_table, c2))
          temp_needed.append((needed_table, c3))
        needed_tables = temp_needed
            

      ext_tables = []
      for (needed_table, table_con) in needed_tables:
        if max_poly in needed_table.keys():
          raise Exception("already done")
        
        # extended single table
        # (needed_table extended by max_poly
        # keeps only the rows corresponding to pols
        ext_single_table = self.extend_single_table(
            needed_table, table_con, max_poly, pols)
        
        # skip if bottom
        if ext_single_table == self.BOTTOM:
          continue
        
        # maps rows of table back to what is in defined in mapping mpg
        mb = self.table_map_back(ext_single_table, needed_polies, mpg)
        # condenses table to only have the rows corresponding to polys
        # (which was the inital goal)
        cond_mb = self.copy_table(mb, polys, table_con)
        ret.append((cond_mb, table_con))

        
    return ret
    
  def extend_single_table(self, table, context, max_poly, pols):
    """Extends a single sign diagram by given polynomial using a
    specific context
    
    Keyword arguments:
    table -- sign diagram to be extended. Must include rows for pols
    and max_poly % pols (using pseudo-division).
    context -- dictionary that associates  constants (with respect to
    the variable to be eliminated) with their sign (-1, 0, 1)
    max_poly -- polynomial that is addded to sign diagram
    pols -- polynomials are going to be present (with addition to max_poly)
    in the returned sign diagram
    
    return -- tuple of sign diagram and context
    """
    
    # inefficient to calculate them here (could do before)
    max_poly_lc = self._algebra.LC(max_poly)
    max_poly_degree = self._algebra.degree(max_poly)
    max_poly_lc_sign = self.sign_context_lookup(context, max_poly_lc)
    
    mp_s_pos_inf = max_poly_lc_sign
    mp_s_neg_inf = (-1)**max_poly_degree * max_poly_lc_sign
    
    
    # copies table such that it is a sign diagram for pols (only one
    # point between roots) - condenses the table
    cond_table = self.copy_table(table, pols, context)
    
    cond_table[max_poly] = {}
    cond_table[max_poly][Fraction(0)] = mp_s_neg_inf
    cond_table[max_poly][Fraction(1)] = mp_s_pos_inf

    # needs to be sorted to filter out infinity values
    cols = sortedset(cond_table[pols[0]].keys())
    
    # early return for constant
    if max_poly_degree == 0:
      for col in cols[1:-1]:
        cond_table[max_poly][col] = max_poly_lc_sign
      return cond_table

    
    # determine the polynomial values on roots of other polynomials
    for p in pols:
      # zero polynomial
      if cond_table[p][Fraction(0)] == 0:
        continue
      # iterate over non-infinity columns  
      for col in cols[1:-1]:
        # not a roots, so skip
        if cond_table[p][col] != 0:
          continue
          
        # remainder of max_poly pseudo divided by p
        rem = self._algebra.pseudo_div(max_poly, p)[1]
        
        # lookup the remainder's value from the original table
        max_poly_value = self.table_lookup(
          table, rem, col, context)

        p_lc = self._algebra.LC(p)
        
        if self._algebra.has_variable(p_lc) & \
           (context.has_key(p_lc) == False):
          raise Exception("variable lc is not yet implemented")
        pseudo_neg = self.sign_context_lookup(context, p_lc) < 0
        # degree of pseudo coefficient
        pseudo_deg = self._algebra.degree(max_poly) - \
                 self._algebra.degree(p) + 1
        pseudo_odd_deg = pseudo_deg % 2 == 1

        # flip the sign if leading coefficient of p is negative
        # and pseudo coefficient is lc of p to an odd power
        if pseudo_neg & pseudo_odd_deg:
          max_poly_value = -max_poly_value

        cond_table[max_poly][col] = max_poly_value
    
    # gets all columns and then zips them with indexes
    cols = sortedset(cond_table[pols[0]].keys())
    zipped_cols = zip(cols, range(len(cols)))
    
    # determine values at unknown points
    for (cur_col, ind) in zipped_cols[:-1]:
      # value is known
      if cond_table[max_poly].has_key(cur_col):
        continue
        
      # next column
      next_col = zipped_cols[ind + 1][0]
      # previous column
      prev_col = zipped_cols[ind - 1][0]
      

      prev_val = cond_table[max_poly][prev_col]
      next_val = cond_table[max_poly][next_col]
      
      if (prev_val == 0) & (next_val == 0):
        return self.BOTTOM
      elif (prev_val + next_val) == 0:
        # opposite sign, create two new columns
        left_new_col = (prev_col + cur_col) / 2
        right_new_col = (cur_col + next_col) / 2

        # set values for max_poly
        cond_table[max_poly][left_new_col] = prev_val
        cond_table[max_poly][right_new_col] = next_val
        cond_table[max_poly][cur_col] = 0

        # set other polynomials in the two created columns
        for p in pols:
          p_val = cond_table[p][cur_col]
          cond_table[p][left_new_col] = p_val
          cond_table[p][right_new_col] = p_val
      else:
        # they are either both the same sign or one is zero
        # copy the nonzero sign of the neighbouring column
        cond_table[max_poly][cur_col] = \
              self._algebra.sign(prev_val + next_val)
    
    return cond_table
  
  def table_map_back(self, table, pols, mapping):
    """Creates a new table such that polynomials in pols are
    mapped to polynomials given in mapping.
    
    Rows that cannot be mapped remain unchanged.
    
    Keyword arguments:
    table -- table which rows are mapped back
    pols -- polynomials have been mapped to something (and are
    now mapped back)
    mapping -- defines mapping between pols and table
    """
    
    # returned table
    ret = {}
    # columns that have been mapped back
    pset = set(table.keys())
    for pol in pols:
      ret[pol] = {}
      # everything should be mapped to something
      # (even if they were mapped to themselves)
      if (mapping.has_key(pol) == False):
        raise Exception("doesn't have a key")
      # copy row based on the mapping
      ret[pol] = table[mapping[pol]].copy()
      if pol in pset:
        pset.remove(pol)
        
    # copy rows that weren't a mapping of anything    
    for pol in pset:
      ret[pol] = {}
      ret[pol] = table[pol].copy()
    return ret
    

  def sign_context_lookup(self, context, key):
    if self._algebra.has_variable(key) == False:
      return self._algebra.sign(key)

    if context.has_key(key) == False:
      raise Exception("no key (%s) in context (%s)" %(key, context))
    return context[key]
    

  def get_initial_table(self, poly, context):
    """Retuns sign diagram when there is only one polynomial
    
    Keyword arguments:
    poly -- polynomial that is going to be a row in sign_diagram
    context -- dictionary that associates  constants (with respect to
    the variable to be eliminated) with their sign (-1, 0, 1)
    
    return -- list of tuples of sign_diagram and context
    """
    poly_lc = self._algebra.LC(poly)
    poly_degree = self._algebra.degree(poly)


    if poly_degree > 0:
      raise Exception("should be never reached now")
      
    # no variables, just return the constant row of the sign
    if self._algebra.has_variable(poly_lc) == False:
      # scalar values
      poly_lc_sign = self._algebra.sign(poly_lc)
      ret_table = {}
      ret_table[poly] = {}
      # need to have three, because the next polynomial is
      # going to be known in inifinite values and uses the
      # fact that is not known at a middle value to possible
      # extend the table
      ret_table[poly][Fraction(0)] = poly_lc_sign
      ret_table[poly][Fraction(1,2)] = poly_lc_sign
      ret_table[poly][Fraction(1)] = poly_lc_sign
      return [(ret_table, context)]
    
    if context.has_key(poly_lc):
      ret_table = {}
      ret_table[poly] = {}
      sign = self.sign_context_lookup(context, poly_lc)
      # need to have three, because the next polynomial is
      # going to be known in inifinite values and uses the
      # fact that is not known at a middle value to possible
      # extend the table
      ret_table[poly][Fraction(0)] = sign
      ret_table[poly][Fraction(1,2)] = sign
      ret_table[poly][Fraction(1)] = sign
      return [(ret_table, context)]
    
    # this part should be reached only when eliminating
    # single constant polynomials (otherwise) derivative should
    # set the the value for leading coefficient
    
    c1 = context.copy()
    c2 = context.copy()
    c3 = context.copy()
    c1[poly_lc] = -1
    c2[poly_lc] = 0
    c3[poly_lc] = 1
    r1 = self.get_initial_table(poly, c1)
    r2 = self.get_initial_table(poly, c2)
    r3 = self.get_initial_table(poly, c3)
    return r1 + r2 + r3
    if context.has_key(poly) == False:
      raise Exception("might reach this")
    ret_table = {}
    ret_table[poly] = {}
    ret_table[poly][Fraction(0)] = context[poly]
    ret_table[poly][Fraction(1,2)] = context[poly]
    ret_table[poly][Fraction(1)] = context[poly]
    return [(ret_table, context)]

    # TODO need to remember why variable is always setted
    # probably because of context extension.
    raise Exception("should be never reached now")

    if self._algebra.has_variable(poly_lc):
      if context.has_key(poly_lc):
        signs_contexes = [context]
      else:
        c1 = context.copy()
        c2 = context.copy()
        c3 = context.copy()
        c1[poly_lc] = -1
        c2[poly_lc] = 0
        c3[poly_lc] = 1
        signs_contexes = [c1, c2, c3]
    else:
      signs_contexes = [context]

    ret = []
    for context in signs_contexes:
      lc_sign = self.sign_context_lookup(context, poly_lc)
      if lc_sign != 0:
        table = {}
        table[poly] = {}
        table[poly][Fraction(1)] = lc_sign
        table[poly][Fraction(0)] = (-1)**poly_degree * lc_sign

        #only polynomial, first degree
        table[poly][Fraction(1,2)] = table[poly][Fraction(0)]

        #check that has eliminated variable
        if poly_degree == 1:
          table[poly][Fraction(1,2)] = 0
        else:
          # can also be constant
          table[poly][Fraction(1,2)] = table[poly][Fraction(0)]
        table[poly][Fraction(3,4)] = table[poly][Fraction(1)]
        ret.append((table, context))
      else:
        tail = poly - self._algebra.LT(poly)
        if context.has_key(tail):
          contexes2 = [context]
        else:
          c1 = context.copy()
          c2 = context.copy()
          c3 = context.copy()
          c1[tail] = -1
          c2[tail] = 0
          c3[tail] = 1
          contexes2 = [c1, c2, c3]
        for c2 in contexes2:
          table = {}
          table[poly] = {}
          for c in [Fraction(0), Fraction(1,4), Fraction(1,2), Fraction(3,4), Fraction(1)]:
            table[poly][c] = self.sign_context_lookup(c2, tail)
          ret.append((table, c2))
    return ret

  def expand_context(self, context, polies, mapping):
    """ Expands the contexts by setting the leading coefficient of poly
    either negative, positive or zero (if it has variable). When it is
    zero then does the same for the next coefficient etc.
    
    keyword arguments:
    context -- context to be extended (can't have y>0 and y<0 in the same
    context).
    polies -- polies to be extended.
    mapping -- mapping from old poly to new one.
    
    return -- list of triplets (context, polies, mapping). Each element
    corresponds to particular extension.
    """
    
    # if no polynomials, just return
    if len(polies) == 0:
      return [(context, [], mapping)]

    head = polies[0]
    head_tail = self._algebra.p_tail(head)
    rest = polies[1:]

    # expand the tail
    expanded_rest = self.expand_context(context, rest, mapping)
    lc_head = self._algebra.LC(head)

    
    if self._algebra.has_variable(lc_head) == False:
      #never satisfied, these kind of coefs should be discarded
      if (head != 0) & (lc_head == 0):
        raise Exception("coef is zero: %s" %lc_head)
      
      # polynomial can't be assigned to get a lower order one
      # so add just to polynomials and create a mapping to itself
      for (con, ps, mpng) in expanded_rest:
        # polynomials stays the same
        mpng[head] = head
        # add polynomial to list
        ps.insert(0, head)
      return expanded_rest

    # lc_head has variable by this point
    
    ret = []
    for (con, ps, mpng) in expanded_rest:
      possible_signs = []

      if con.has_key(lc_head):
        # if context has variable then just use the value
        lc_sign = self.sign_context_lookup(con, lc_head)
        possible_signs = [lc_sign]
      else:
        # if not then add all possibilities
        possible_signs = [-1, 0, 1]
        
      for sign in possible_signs:
        con_copy = con.copy()
        ps_copy = list(ps)
        
        #no effect if assignment was already there
        con_copy[lc_head] = sign
        
        if sign != 0:
          # poly can't be extended if sign != 0
          ps_copy.append(head)
          mapping_copy = mpng.copy()
          #copy add mapping to what ever was gotten from recursive call
          mapping_copy[head] = head
          ret.append((con_copy, ps_copy, mapping_copy))
        else: #sign == 0
          #extend the tail of the polynomial (since lc was zero)
          h_t_expanded = self.expand_context(con_copy, [head_tail], mpng)
          
          for (con2, ps2, mpng2) in h_t_expanded:
            mapping_copy = mpng2.copy()
            # add mapping to mapping gotten from rec. call
            mapping_copy[head] = mpng2[head_tail]
            ret.append((con2, ps_copy + ps2, mapping_copy))
    return ret


  def copy_table(self, table, needed_polies, context):
    """Copies the diagram such that it includes only some of
    the polynomials, but still is a correct sign diagram
    (has exactly one column between roots that are not roots
    or infinity columns)
    
    Keyword arguments:
    table -- table to be copied (/reduced)
    needed_polies -- polynomials that are included in new table
    context -- context that was used to get the table
    
    return -- sign diagram with needed_polies as rows
    """
    ret = {}
    if len(needed_polies) == 0:
      return ret

    #needs to be sorted
    #table columns
    t_cols = sortedset(table[table.keys()[0]].keys())
    z_cols = zip(t_cols, range(len(t_cols)))
    copy_cols = sortedset([Fraction(0), Fraction(1)])

    #get all the roots of needed polynomials and points between them
    #except for the first root of all (need to copy manually)
    for p in needed_polies:
      if table.has_key(p) == False:
        continue
      if table[p][Fraction(0)] == 0:
        continue
      for (col, ind) in z_cols[1:-1]:
        if table[p][col] == 0:
          copy_cols.add(col)
          copy_cols.add(z_cols[ind + 1][0])

    #copies all the roots and points immediately after them
    for p in needed_polies:
      ret[p] = {}
      for col in copy_cols:
        ret[p][col] = self.table_lookup(table, p, col, context)

      # manual copy of the point before first root
      # this must exist in the table
      # this is the same as for -infinity
      point_before_first = (copy_cols[1] + copy_cols[0]) / 2
     
      ret[p][point_before_first] = self.table_lookup(
        table, p, copy_cols[0], context)
    return ret
  
  def table_lookup(self, table, p, col, context):
    if self._algebra.degree(p) > 0:
      return table[p][col]
    if self._algebra.has_variable(p) == False:
      return self._algebra.sign(p)
    if context.has_key(p):
      return context[p]
    raise Exception("context lookup")

  def pprint_diagram(self, diagram):
    if len(diagram) == 0:
      print "Empty table"
      return
    """Pretty prints diagram"""
    max_len = sortedset(map(lambda s: len(str(s)), diagram.keys()))[-1]
    header = sortedset()
    for row in diagram.keys():
      header.update(diagram[row].keys())
    #print map(lambda x: x, header)
    print "-" * max_len
    for row in sortedset(diagram.keys()):
      print str("%%%ds   " %max_len) %row,
  #     print "%s " %diagram[row],
  #     for index in diagram[row].keys():
  #       print "%2s " %diagram[row][index][0],
      for col in header:
        if col in diagram[row]:
          print "%2s" %diagram[row][col],
        else:
          print " *",
      print ""
    print ""
