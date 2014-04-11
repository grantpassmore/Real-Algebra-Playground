from blist import sortedset
import sympy


x,y,z, x0, x1, x2 = sympy.var('x,y,z, x0, x1, x2')
class CohenHormander:

  def __init__(self, algebra):
    self._algebra = algebra

  def real_full(self, equalities):
    polys = equalities # TODO add lessers and greaters
    contexted_tables = self._real_table(polys, {}, -1)
    for table, c in contexted_tables:
      print c
      self.pprint_diagram(table)

  def foo(self, polys, context, iter):
#    try:
      self._real_table(polys, context, iter)
#    except Exception as e:
#      print e.message


  def _real_table(self, polys, context, iter):
    if iter < 0:
      raise Exception("iter")
    if len(polys) == 0:
      return {}

    set = sortedset(polys, key = lambda p: - self._algebra.degree(p))
    # pick the next polynomial (which is of maximum degree)
    max_poly = set.pop(0)
    derivative = self._algebra.derivative(max_poly)

    # polynomials needed (all other + plus derivative)
    needed_polies = set.copy()
    if (self._algebra.zero() != derivative):
      needed_polies.add(derivative)
    #print "needed polies: %s" %needed_polies
    if len(needed_polies) == 0:
      #print "getting initial"
      contexted_tables = self.get_initial_table(max_poly, context)
      #print contexted_tables
      return contexted_tables
      
    # [context, [pol], mapping]
    exp_contexts = self.expand_context(context, needed_polies, {})

    ret = []
    for (con, pols, mpg) in exp_contexts:
      #print "con: %s" %con
      #print "pols: %s" %pols
      # calculate division when not constant
      rems = map(
        lambda g: self._algebra.pseudo_div(max_poly, g)[1], 
        filter(lambda g: self._algebra.degree(g) >= 0, pols)
      )
      new_goal = filter(
        lambda p: self._algebra.degree(p) >= 0, 
        pols + rems
      )
      #print "rems: %s" %rems
      #print "new_goal: %s" %new_goal
      needed_tables = self._real_table(new_goal, con, iter - 1)

      ext_tables = []
      for (needed_table, table_con) in needed_tables:
        """print "in loop2"
        print "old_goal: %s" %polys
        print "max_poly: %s" %max_poly
        print "new_goal: %s" %new_goal
        print "table_con %s" %table_con
        print "mpg: %s" %mpg
        print "tabel for %s" %new_goal
        self.pprint_diagram(needed_table)
        """
        max_poly_lc = self._algebra.LC(max_poly)
        max_poly_degree = self._algebra.degree(max_poly)
        max_poly_lc_sign = self.sign_context_lookup(table_con, max_poly_lc)

        if max_poly in needed_table.keys():
          raise Exception("already done")
    
        table_temp = self.copy_table(needed_table, pols, table_con)

        mapped_back_table = self.table_map_back(table_temp, pols, mpg)

        mapped_back_table[max_poly] = {}
        mapped_back_table[max_poly][1.0] = max_poly_lc_sign
        mapped_back_table[max_poly][0.0] = (-1)**max_poly_degree * max_poly_lc_sign

        # needs to be sorted to filter out infinity values
        cols = sortedset(mapped_back_table[pols[0]].keys())

        # determine the polynomial values on roots of other polynomials
        # should probably be needed_polies
        for p in pols:
          #print "p: %s" %p
          if mapped_back_table[p][0.0] == 0:
            continue
          for col in cols[1:-1]:
            if mapped_back_table[p][col] == 0:
              print p
              rem = self._algebra.pseudo_div(max_poly, p)[1]
              max_poly_value = self.table_lookup(
                mapped_back_table, rem, col, table_con)

              p_lc = self._algebra.LC(p)
              if self._algebra.has_variable(p_lc) & \
                 (table_con.has_key(p_lc) == False):
                raise Exception("variable lc is not yet implemented")
              p_neg = self.sign_context_lookup(table_con, p_lc) < 0
              p_deg = self._algebra.degree(max_poly) - \
                       self._algebra.degree(p) + 1
              p_odd_deg = p_deg % 2 == 1

              if p_neg & p_odd_deg:
                max_poly_value = -max_poly_value

              mapped_back_table[max_poly][col] = max_poly_value

        cols = sortedset(mapped_back_table[pols[0]].keys())
        zipped_cols = zip(cols, range(len(cols)))
        
        # determine values at unknown points
        for (cur_col, ind) in zipped_cols[:-1]:
          next_col = zipped_cols[ind + 1][0]
          prev_col = zipped_cols[ind - 1][0]
          # already empty column
          if mapped_back_table[max_poly].has_key(cur_col):
            continue

          prev_val = mapped_back_table[max_poly][prev_col]
          next_val = mapped_back_table[max_poly][next_col]
          if (prev_val == 0) & (next_val == 0):
            raise Exception("both zero")
          elif (prev_val + next_val) == 0: # opposite sign
            left_new_col = (prev_col + cur_col) / 2
            right_new_col = (cur_col + next_col) / 2

            mapped_back_table[max_poly][left_new_col] = prev_val
            mapped_back_table[max_poly][right_new_col] = next_val
            mapped_back_table[max_poly][cur_col] = 0

            for p in pols:
              p_val = mapped_back_table[p][cur_col]
              mapped_back_table[p][left_new_col] = p_val
              mapped_back_table[p][right_new_col] = p_val
          else:
            # they are either both the same sign or one is zero
            mapped_back_table[max_poly][cur_col] = \
                  self._algebra.sign(prev_val + next_val)

        #print "mapped back31: "
        #self.pprint_diagram(mapped_back_table)
        #print table_con
        ret.append((mapped_back_table, table_con))
    #print 
    for t, c in ret:
      #print c
      #self.pprint_diagram(t)
      continue
#      raise Exception("loop")

    return ret
    rems = map(
      lambda g: self._algebra.pseudo_div(max_poly, g)[1], 
      needed_polies
    )

    new_goal = filter(
      lambda p: self._algebra.degree(p) > 0, 
      [derivative] + map(lambda p: p, set) + rems
    )

    needed_table = self._real_table(new_goal, context, iter - 1)
    print "tabel for %s" %new_goal
    self.pprint_diagram(needed_table)

    max_poly_lc = self._algebra.LC(max_poly)
    max_poly_degree = self._algebra.degree(max_poly)
    max_poly_lc_sign = self._algebra.sign(max_poly_lc)
    
    if max_poly in needed_table.keys():
      raise Exception("already done")
    
    table = self.copy_table(needed_table, needed_polies, {})
    
    table[max_poly] = {}
    table[max_poly][1.0] = max_poly_lc_sign
    table[max_poly][0.0] = (-1)**max_poly_degree * max_poly_lc_sign

    #only polynomial, first degree
    if len(needed_polies) == 0:
      table[max_poly][0.25] = table[max_poly][0.0]
      print "max_poly_deg: %s" %max_poly_degree
      #chack that has eliminated variable
      if max_poly_degree == 1:
        table[max_poly][0.5] = 0
      else:
        # can also be constant
        table[max_poly][0.5] = table[max_poly][0.0]
      table[max_poly][0.75] = table[max_poly][1.0]
      return table

    # needs to be sorted to filter out infinity values
    cols = sortedset(table[needed_polies[0]].keys())

    # determine the polynomial values on roots of other polynomials
    for p in needed_polies:
      for col in cols[1:-1]:
        if table[p][col] == 0:
          rem = self._algebra.pseudo_div(max_poly, p)[1]
          max_poly_value = self.table_lookup(needed_table, rem, col, {})

          p_lc = self._algebra.LC(p)
          if self._algebra.has_variable(p_lc):
            raise Exception("variable lc is not yet implemented")
          p_neg = p_lc < 0
          p_deg = self._algebra.degree(max_poly) - \
                   self._algebra.degree(p) + 1
          p_odd_deg = p_deg % 2 == 1

          if p_neg & p_odd_deg:
            max_poly_value = -max_poly_value

          table[max_poly][col] = max_poly_value


    cols = sortedset(table[needed_polies[0]].keys())
    zipped_cols = zip(cols, range(len(cols)))

    # determine values at unknown points
    for (cur_col, ind) in zipped_cols[:-1]:
      next_col = zipped_cols[ind + 1][0]
      prev_col = zipped_cols[ind - 1][0]
      # already empty column
      if table[max_poly].has_key(cur_col):
        continue
      
      prev_val = table[max_poly][prev_col]
      next_val = table[max_poly][next_col]
      if (prev_val == 0) & (next_val == 0):
        raise Exception("both zero")
      elif (prev_val + next_val) == 0: # opposite sign
        left_new_col = (prev_col + cur_col) / 2
        right_new_col = (cur_col + next_col) / 2
        
        table[max_poly][left_new_col] = prev_val
        table[max_poly][right_new_col] = next_val
        table[max_poly][cur_col] = 0

        for p in needed_polies:
          p_val = table[p][cur_col]
          table[p][left_new_col] = p_val
          table[p][right_new_col] = p_val
      else:
        # they are either both the same sign or one is zero
        table[max_poly][cur_col] = self._algebra.sign(prev_val + next_val)

#    return self.copy_table(table, polys)

  def table_map_back(self, table, pols, mpg):
    ret = {}
    for pol in pols:
#      print "pol: %s" %pol
      ret[pol] = {}
      if (mpg.has_key(pol) == False):
        raise Exception("doesn't have a key")
      ret[pol] = table[mpg[pol]].copy()
    return ret

  def sign_context_lookup(self, context, key):
    if self._algebra.has_variable(key) == False:
      return self._algebra.sign(key)

    if context.has_key == False:
      raise Exception("no key (%s) in context (%s)", key, context)
    return context[key]
    

  def get_initial_table(self, poly, context):
#    print "initial poly: %s" %poly
#    print "intial context: %s" %context
    poly_lc = self._algebra.LC(poly)
    poly_degree = self._algebra.degree(poly)

    if poly_degree <= 0:
      # no variables, just return the constant row of the sign
      if self._algebra.has_variable(poly_lc) == False:
        poly_lc_sign = self._algebra.sign(poly_lc)
        ret_table = {}
        ret_table[poly] = {}
        ret_table[poly][0.0] = poly_lc_sign
        ret_table[poly][0.5] = poly_lc_sign
        ret_table[poly][1.0] = poly_lc_sign
        return [(ret_table, context)]
      else:
        print "poly: %s" %poly
        print "context: %s" %context
        if context.has_key(poly) == False:
          raise Exception("might reach this")          
        ret_table = {}
        ret_table[poly] = {}
        ret_table[poly][0.0] = context[poly]
        ret_table[poly][0.5] = context[poly]
        ret_table[poly][1.0] = context[poly]
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
        table[poly][1.0] = lc_sign
        table[poly][0.0] = (-1)**poly_degree * lc_sign

        #only polynomial, first degree
        table[poly][0.25] = table[poly][0.0]

        #check that has eliminated variable
        if poly_degree == 1:
          table[poly][0.5] = 0
        else:
          # can also be constant
          table[poly][0.5] = table[poly][0.0]
        table[poly][0.75] = table[poly][1.0]
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
          for c in [0.0, 0.25, 0.5, 0.75, 1.0]:
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
    
    if len(polies) == 0:
      return [(context, [], mapping)]

    head = polies[0]
    head_tail = self._algebra.p_tail(head)
    rest = polies[1:]

    expanded_rest = self.expand_context(context, rest, mapping)
    lc_head = self._algebra.LC(head)

    """
    print "<context: %s" %context
    print "exp polies: %s" %polies    
    """
#    print "expanding on: %s" %head
    """
    print "rest: %s" %rest
    print "exp rest: %s" %expanded_rest
    print "lc_head: %s" %lc_head
    """
    
    if self._algebra.has_variable(lc_head) == False:
      "never satisfied, these kind of coefs should be discarded"
      if (head != 0) & (lc_head == 0):
        raise Exception("coef is zero: %s" %lc_head)
      for (con, ps, mpng) in expanded_rest:
        mpng[head] = head
        ps.insert(0, head)
      return expanded_rest

    #lc_head has variable by this point
    ret = []
    for (con, ps, mpng) in expanded_rest:
      possible_signs = []

      if con.has_key(lc_head):
        lc_sign = self.sign_context_lookup(con, lc_head)
        possible_signs = [lc_sign]
      else:
        possible_signs = [-1, 0, 1]
      for sign in possible_signs:
        con_copy = con.copy()
        ps_copy = list(ps)
        #no effect if already done
        con_copy[lc_head] = sign
        if sign != 0:
          ps_copy.append(head)
          mapping_copy = mpng.copy()
          mapping_copy[head] = head
          if( head == (x*x2 + x1)):
            print "#here"
            print "###h: %s" %head

            print mapping_copy            

          ret.append((con_copy, ps_copy, mapping_copy))
        else: #sign == 0
          h_t_expanded = self.expand_context(con_copy, [head_tail], mpng)
          for (con2, ps2, mpng2) in h_t_expanded:
            mapping_copy = mpng2.copy()
            mapping_copy[head] = mpng2[head_tail]
            ret.append((con2, ps_copy + ps2, mapping_copy))
    return ret


  def copy_table(self, table, needed_polies, context):
    ret = {}
    if len(needed_polies) == 0:
      return ret

    #needs to be sorted
    #table columns
    t_cols = sortedset(table[table.keys()[0]].keys())
    z_cols = zip(t_cols, range(len(t_cols)))
    copy_cols = sortedset([0.0, 1.0])

    #get all the roots of needed polynomials and points between them
    #except for the first root of all (need to copy manually)
    for p in needed_polies:
      if table.has_key(p) == False:
        continue
      if table[p][0.0] == 0:
        continue
      for (col, ind) in z_cols[1:-1]:
        if table[p][col] == 0:
          copy_cols.add(col)
          copy_cols.add(z_cols[ind + 1][0])

    #copies all the roots and points immediately after them
    for p in needed_polies:
      ret[p] = {}
      for col in copy_cols:
        """
        #copy from context when it is scalar
        if table.has_key(p) == False:
          if context.has_key(p) == False:
            print "here1"
            raise Exception("no key (%s) in context (%s) and table\n%s" 
                            %(p, context, self.pprint_diagram(table) ))
          ret[p][col] = context[p]
          continue
        ret[p][col] = table[p][col]"""
        ret[p][col] = self.table_lookup(table, p, col, context)

      # manual copy of the point before first root
      # this must exist in the table
      # this is the same as for -infinity
      point_before_first = (copy_cols[1] + copy_cols[0]) / 2
      """
      print point_before_first
      if table.has_key(p) == False:
        if context.has_key(p) == False:
          raise Exception("no key in table and context")
        ret[p][col] = context[p]
        ret[p][point_before_first] = context[p]
        continue
      ret[p][point_before_first] = table[p][copy_cols[0]]"""
      ret[p][point_before_first] = self.table_lookup(
        table, p, copy_cols[0], context)
    print copy_cols
    print "copy ret"
    self.pprint_diagram(ret)
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
