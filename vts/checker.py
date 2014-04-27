import time

import sympy

import examples_parser
import isym

import prog_printer as prog

def check_examples(vts=True):
  uni_ex_files= examples_parser.unpickle_dirs_gen()

  prog.reset()
  skip = {(3, 0)}
  skip = {}
  
  for file_index, example_file in enumerate(uni_ex_files):
    prog.p("file nr.%d" %file_index)
    if file_index < 1:
      continue
    if file_index > 1:
      break
    prog.inc()
    for ex_index, example in enumerate(example_file):
      if ex_index < 0:
        continue
      if ex_index > 99:
        break;
      prog.p("using example nr.%d" %ex_index)
      
      if (file_index, ex_index) in skip:
        prog.p("skipping")
        continue
      uni_ante, uni_succ = example

      prog.p("antecedent len: %s" %len(uni_ante))
      prog.p("succedent len: %s" %len(uni_succ))
      prog.inc()

      formula_value = True
      #if big_or has a clause that is true then original formula is false
      big_or = vts_preformat(uni_ante, uni_succ)
      for formula in big_or:
        # print "checking formula: %s" %formula
        r_map = make_relation_map(formula)

        """
        print "le: %s" %r_map['le']
        print "lt: %s" %r_map['lt']
        print "eq: %s" %r_map['eq']
        print "ne: %s" %r_map['ne']
        #"""
#        return 
        if vts:
          disj_value = \
              isym.vts(r_map['le'], r_map['lt'], r_map['eq'], r_map['ne'])
        else:
          disj_value = \
              isym.ts(r_map['le'], r_map['lt'], r_map['eq'], r_map['ne'])


        prog.p("disj_value: %s" %disj_value)
        if disj_value:
          formula_value = False
      prog.p("formula value: %s" %formula_value)
      prog.dec()
    prog.dec()

def make_relation_map(formula):
  """Distributes relations in formula to map based on their type (<=, <, =, !=)
  
  Keyword arguments:
  formula -- formula where relations are (assumes rhs is zero)
  
  return -- map of relations (keys are types, values are lists of corresponding
  relations)
  """
  lookup = {sympy.Le: 'le', sympy.Lt: 'lt', sympy.Eq: 'eq', sympy.Ne: 'ne'}
  r_map = {'le':[], 'lt': [], 'eq': [], 'ne': []}
  for relation in formula:
    added = False
    for cls in lookup:
      if isinstance(relation, cls):
        r_map[lookup[cls]].append(relation.lhs)
        added = True
        # no need to continue, since there can be only one match
        break
    if not added:
      raise Exception("relation: %s, wasn't added" %relation)
  return r_map

def vts_preformat(uni_ante, uni_succ):
  """Preformats formula to more easily checkable one.
  Uses the following property:
  p => q is false when p /\ not(q) is true.
  If q = q1 /\ q2 /\ .. qn then this becomes
  p /\ ((not(q1) \/ not(q2) .. \/ qn)) which can be rewritten to more easily
  checkable p /\ not(q1) \/ p /\ not(q2) .. p /\ \/ qn)
  
  Keyword arguments:
  uni_ante -- antecedent of the formula (univariate)
  uni_ante -- succedent of the formula (univariate)
  
  return -- lists of clauses. if any of these is satisfiable then initial
  is not tautology.
  """
  
  # filter out True's
  filtered_ante = set(filter(lambda p: not (p == True), uni_ante))
  filtered_succ = set(filter(lambda p: not (p == True), uni_succ))
  
  # TODO
  if len(filtered_ante) == 0 or len(filtered_succ) == 0:
    raise Exception('antecedent or succedent became zero')
  
  
  # rewrite everything > and >= (to < and <=)
  # also negate the succedent
  rewritten_ante = rewrite_to_less(filtered_ante)
  negated_succ = negate_relations(filtered_succ)
  rewritten_succ = rewrite_to_less(negated_succ)
  
  """print
  print uni_ante
  print rewritten_ante
  print uni_succ
  print negated_succ
  print rewritten_succ
  """
  
  #distribute the antecedent over succedent
  ret = []
  for succ in rewritten_succ:
    tempList = list(rewritten_ante)
    tempList.append(succ)
    ret.append(tempList)
  return ret

def rewrite_to_less(relations):
  """Rewrites relation to not include > and >=
  
  Keyword arguments:
  relation -- relation to be rewritten
  
  return -- rewritten relation
  """
  
  # map of to be rewritten relations
  rewrite_classes = {sympy.Ge: sympy.Le, sympy.Gt: sympy.Lt}
  ret = []
  for relation in relations:
    cls = relation.__class__
    if not cls in rewrite_classes:
      ret.append(relation)
      continue
    # dual relation
    rcls = rewrite_classes[cls]
    # construct and append the equiavalent relation
    ret.append(rcls(-relation.lhs, -relation.rhs))
  return ret
  
def negate_relations(relations):
  """Negates a relation
  
  Keyword arguments:
  relations -- lists of relations to be negated
  
  return -- lists of negated relations
  """
  
  # map where key - value pairs are contracting relation types
  negation_classes = {
    sympy.Ge: sympy.Lt, sympy.Gt: sympy.Le, 
    sympy.Eq: sympy.Ne, sympy.Ne: sympy.Eq, 
    sympy.Le: sympy.Gt, sympy.Lt: sympy.Ge, 
  }
  return map(lambda ins: negation_classes[ins.__class__](ins.lhs, ins.rhs), \
    relations)
