#########################################################################
# `Geometric Relevance Filtering for Real Quantifier Elimination'       #
#                                                                       #
# Experimenting with ``goal directed'' approaches to RCF reasoning!     #
# A collaboration between Grant, Andre, Erik and Jeremy.                #
#                                                                       #
# Written by Grant Passmore (grant.passmore@cl.cam.ac.uk).              #
# Began on 24-September-2012, Last updated on 15-December-2013.         #
#########################################################################

#
# To-Do ideas:
#   - Incorporate weighting schemes into hypothesis selection...DONE!,
#   - Extend procedure to incorporate `complete/sound/real' CAD
#      (at the end, once our FD procedure thinks the RHS of the
#       goal sequent is True.)
#   - Try out procedure on KeYmaera hiding examples...DONE!,
#   - Try out procedure on MetiTarski benchmarks,
#   - Should we extend Hi hypotheses to have boolean structure (/\, \/)?,
#   - SMTLib 2.0 parser for input problems...DONE!,
#   - Sort candidate hypotheses by degree/weight/#vars/etc
#      (look at p 264 in Andre's book),
#   - Look into not requiring all variables to be in the initial goal. ..DONE!,
#   - Understand where/when B-M projection with normal lifting is sufficient,
#   - Full (Hong-Collins) projection operator,
#   - Quantifiers?
#   - Ask black-box QEPCAD?
#   - Empirically, how often is FD selection of hyps + end-game QEPCAD
#      enough for a YES?
#
#   - Must bias hypothesis selection against equational hypotheses
#     containing only variables that do not appear in the goal.
#     Perhaps this should involve `freezing' certain variables
#     during sample point perturbation over `bad' cells.
#      ...DONE! - 28-Oct-2013
#

from sage.rings.polynomial.real_roots import *
import sage.rings.polynomial.multi_polynomial_libsingular as Singular
import random
import pipes
import tempfile
import sys

import local_search as lss

class RCF:
    pass

#
# A class for building and deciding RCF atoms.
#

class RCF_Atom(RCF):
    def __init__(self, lhs, op, rhs):
        if not(op in [">", "<", "<=", ">=", "=", "!="]):
            raise Exception("Invalid op in RCF_Atom.")
        self.poly = (lhs - rhs)
        self.op = op
        self.vars = self.poly.variables()

    def __str__(self):
        return ("[" + str(self.poly) + " " + self.op + " 0]")

    # Given a Groebner basis for an ideal I, we can reduce the
    # polynomial of an atom based upon it. This injects the poly into
    # the quotient ring QQ[\vec{x}]/I.

    def quotient_ring_inject(self, B):
        R = B[0].parent()
        #print "    Working over: ", R
        print "    Attempting Groebner reduction of poly ", self.poly
        print "     by basis ", B
        new_poly = (R(self.poly)).reduce(B)
        print "      - Old poly: ", self.poly
        print "      - New poly: ", new_poly
        self.poly = new_poly

    def negate(self):
        if self.op == ">":
            self.op = "<="
        elif self.op == "<":
            self.op = ">="
        elif self.op == "<=":
            self.op = ">"
        elif self.op == ">=":
            self.op = "<"
        elif self.op == "=":
            self.op = "!="
        elif self.op == "!=":
            self.op = "="
        else:
            raise Exception("Negating unknown RCF relation.")

    def update_ring(self, R):
        self.poly = R(self.poly)

    # We've now extended this to support general inequalities.  If an
    # atom doesn't have all of its variables instantiated by the given
    # dictionary, then evaluation will return None.

    def eval_on_dict(self, dict):
        #print "Evaluating " + str(self.poly) + " on dict " + str(dict)
        all_vars_in_dict = true
        for v in self.vars:
            all_vars_in_dict = (v in dict) and all_vars_in_dict
            if not all_vars_in_dict:
                break
        if not all_vars_in_dict:
            return None
        else:

            # Sage now requires explicit coercions on substitutions

            R = parent(dict.keys()[0])
            self.poly = R(self.poly)

            # print "Attempting substitution:"
            # print "  Poly: ", str(self.poly)
            # print "   class: ", str(self.poly.__class__.__name__)
            # print "   parent: ", str(parent(self.poly))
            # print "  Dict: ", str(dict)
            # print "   class: ", str(dict.keys()[0].__class__.__name__)
            # print "   parent: ", str(parent(dict.keys()[0]))
            # print

            poly_sign = self.poly.substitute(dict)
            if ((self.op == ">") and (poly_sign > 0)):
                return True
            elif ((self.op == ">=") and (poly_sign >= 0)):
                return True
            elif ((self.op == "<") and (poly_sign < 0)):
                return True
            elif ((self.op == "<=") and (poly_sign <= 0)):
                return True
            elif ((self.op == "=") and (poly_sign == 0)):
                return True
            elif ((self.op == "!=") and (poly_sign != 0)):
                return True
            else:
                return False

#
# Class for RCF goals (sequent succedents), represented in the form
#        (goal_hyp[0] /\ ... goal_hyp[k-1] --> main_goal).
#

class RCF_Goal(RCF):
    def __init__(self, main_goal=None, goal_hyps=[]):
        self.main_goal = main_goal
        self.goal_hyps = goal_hyps
        self.num_antecedent_hyps = 0 # Used for pretty-printing
        self.gb = [] # GBasis induced by equations in goal_hyps

    def __str__(self):

        def num_spaces(self):
            l = self.num_antecedent_hyps
            if l <= 10:
                return "      "
            elif l <= 100:
                return "       "
            elif l <= 1000:
                return "        "
            elif l <= 10000:
                return "         "
            else:
                return "          "

        def imp_str(self):
            if self.goal_hyps != []:
                return "\n        -->\n" + num_spaces(self)
            else:
                return ""

        return (num_spaces(self)
                + join([str(a) for a in self.goal_hyps], (" /\\\n" + num_spaces(self)))
                + imp_str(self) + str(self.main_goal))

    def eval_on_dict(self, d):
        if self.main_goal.eval_on_dict(d):
            return True
        else:
            for gh in self.goal_hyps:
                if gh.eval_on_dict(d) == False:
                    return True
            return False

    def goal_polys(self):
        ps = [h.poly for h in self.goal_hyps]
        gp = self.main_goal.poly
        return [gp] + ps

    def add_goal_hyp(self, gh, use_gbs=False):
        if not(use_gbs):
            self.goal_hyps = self.goal_hyps + [gh]
        else:
            B = self.gb
            if gh.op == '=':
                I = ideal([gh.poly])
                B = I.groebner_basis()
                # Currently, B = I :-)!
                # Simplify current goal_hyps using new gh
                for h in self.goal_hyps:
                    h.quotient_ring_inject(B)
                B = ideal(self.gb + [gh.poly]).groebner_basis()
            if self.gb != []:
                # Simplify new gb using current goal_hyps
                gh.quotient_ring_inject(self.gb)
            self.goal_hyps = self.goal_hyps + [gh]
            # Update our working self.gb in case gh has enriched it
            self.gb = B

#################################################################
# Dynamic CAD projection ordering / variable ranking machinery  #
#################################################################

class ProjOrd(RCF):

    def __init__(self, polys=[], variables=[]):
        self.polys = polys
        self.variables = variables
        self.proj_ord = []
        self.var_stats = {}

    def __str__(self):
        if self.var_stats == {}:
            s = "-- Variable stats haven't been computed yet --"
        else:
            s = "-- Variable stats:\n"
            for v in self.variables:
                s += "   var_stats(" + (str(v)) + ") = " + \
                     ("{max_deg = " + str(self.var_stats[v][0]) + \
                      ", max_tdeg = " + str(self.var_stats[v][1]) + \
                      ", num_tms = " + str(self.var_stats[v][2]) + "}\n")
            s += "-- Final proj_ord (projecting from right to left):\n     " + str(self.proj_ord)
        return s

    def compute_var_stats(self, v):
        monos_in_v = filter((lambda m : v in m.variables()), \
                            [m for p in self.polys for m in p.monomials()])

        if monos_in_v != []:
            num_tms = len(monos_in_v)
            max_deg = max([p.degree(v) for p in self.polys])
            max_tdeg = max([m.total_degree() for m in monos_in_v])
        else:
            num_tms, max_deg, max_tdeg = 0, 0, 0

        self.var_stats[v] = (max_deg, max_tdeg, num_tms)

    def compute_stats(self):
        for v in self.variables:
            self.compute_var_stats(v)

    def compute_proj_ord(self):
        self.compute_stats()
        self.proj_ord = sorted(self.variables, \
                               key = (lambda v : self.var_stats[v]))
        self.proj_ord.reverse()
        return self.proj_ord


#################################################################
# :::::::> Begin core full-dimensional Ex RCF CAD code <::::::: #
#################################################################

class QE_Factory(RCF):

    def __init__(self, num_vars):
        self.proj_sets = {(num_vars-1):[]}
        self.num_vars = num_vars
        #
        # When univariate, need to explicitly work over QQ['x0']
        # because there is no canonical coercion in Sage (2013+)
        # between PolynomialRing(QQ, 'x', 1) and
        # PolynomialRing(QQ, 'x', 2).
        #
        if num_vars == 1:
            self.R = QQ['x0']
        else:
            self.R = PolynomialRing(QQ, 'x', num_vars, order='degrevlex')
        # Note: The following assignment allows us to reference
        # self.R's indeterminates as self.x[i]!
        self.x = self.R.gens()
        self.cell_sps = {} # Sample points from each f.d. cell
        # A list of substitution dictionaries for num_vars-dimensional
        # sample points sufficient for deciding AND-OR combinations of
        # strict inequalities involving the input polynomials:
        self.final_sp_dicts = []
        # Declare a projection ordering as a list of indeterminates.
        # Initially, this is just self.x, i.e., [x[0], x[1], ...].
        self.proj_ord = self.x

    #
    # Add a poly or list of polys to top-level projection set.
    #

    def install_polys(self, p, *ps):
        self.proj_sets[self.num_vars - 1].append(p)
        for p in ps:
            self.proj_sets[self.num_vars - 1].append(p)

    #
    # Compute an optimal projection ordering.
    #

    def compute_proj_ord(self):
        po = ProjOrd(polys=self.proj_sets[self.num_vars - 1], \
                     variables = self.x)
        self.proj_ord = po.compute_proj_ord()
        print str(po)

    #
    # If a poly is a pure power of the form (c_i x_i^d), then return
    # the base (x_i). Otherwise, return poly unchanged.
    #

    def pure_poly_base(self, p):
        if (p == p.lt()):
            vs = p.variables()
            if len(vs) == 1:
                return vs[0]
            else:
                return p
        else:
            return p

    #
    # Filter polynomials (at any projection level) which can be
    # cheaply seen to be unnecessary for CAD tree construction.
    # This currently:
    #  - removes all rational constants,
    #  - replaces all polys of the form (c_i x_i^d) with (x_i)
    #     (duplicates are cleared using set()).
    #

    def filter_proj_set(self, ps):
        ps_1 = filter((lambda p: not(p.is_constant())), ps)
        ps_2 = list(set(map(self.pure_poly_base, ps_1)))
        # return ps_2
        # disabling ps_2 filtering for testing 13-Jun
        return ps_2 # Is this ok?

    #
    # Given a list of polys PS and a current indeterminate index i
    #  s.t. ps \subset QQ[x_0, ..., x_i]
    # compute BM-PROJ(ps) \subset QQ[x_0, ..., x_{i-1}]
    #  where BM-PROJ is the Brown-McCallum projection operator.
    #
    # * Note that Sage indexes n indeterminates as x_0 ... x_{n-1}.
    #

    def bm_proj(self, i):
        x_to_elim = self.proj_ord[i]
        ps = set(self.proj_sets[i])
        if len(ps) > 1:
            resultants = [Singular.MPolynomial_libsingular.resultant(p1, p2, x_to_elim)
                          for p1 in ps for p2 in ps if p1 != p2]
        else:
            resultants = []
        print "       .r(" + str(len(resultants)) + ").",
        discriminants = [Singular.MPolynomial_libsingular.discriminant(p, x_to_elim)
                         for p in ps]
        print ".d(" + str(len(discriminants)) + ").",
        lcs = [Singular.MPolynomial_libsingular.coefficient(p, {x_to_elim : p.degree(x_to_elim)}) for p in ps]
        print ".c(" + str(len(lcs)) + ").",
        new_ps = set(resultants + discriminants + lcs)
        filtered_ps = self.filter_proj_set(new_ps)
        self.proj_sets[i-1] = filtered_ps
        print (".f(before=" + str(len(new_ps)) +
               ", after=" + str(len(filtered_ps)) + ").")

    #
    # The projection phase: Compute a full (filtered) Brown-McCallum
    # hierarchy of projection sets, bound to self.proj_sets.  Note
    # that we currently don't compute projection factor sets, only
    # projection sets.  (This affects neither completeness nor
    # soundness, only efficiency.)
    #

    def projection_phase(self):
        print "-- Projection phase:"
        print ("   Top-level polynomials over QQ[x0,..,x"
               + str(self.num_vars-1) + "]:")
        print "      ",
        top_ps = self.proj_sets[self.num_vars-1]
        print top_ps
        self.proj_sets[self.num_vars-1] = self.filter_proj_set(top_ps)
        print "   Filtered: ", self.proj_sets[self.num_vars-1]
        print "\n-- Beginning dynamic projection variable reordering."
        self.compute_proj_ord()
        print "-- Dynamic projection variable reordering complete.\n"
        if self.num_vars <= 1:
            pass
        else:
            for i in range(0, self.num_vars-1):
                print ("    Projecting R^" + str(self.num_vars-i) +
                       " --> R^" + str(self.num_vars-i-1))
                self.bm_proj(self.num_vars-i-1)
                print "       ... Done!"
            print ".:. Projection sets bound to self.proj_sets dictionary."
            print "Proj sets: ", self.proj_sets

    #
    # Construct a list of pairwise disjoint isolating intervals for
    #  roots of a given set of (implicitly) univariate polys. To do
    #  this, we must first convert the given polys from multivariate
    #  polynomial objects into univariate ones. This coercion then
    #  gives us access to the real_root_intervals() method.
    #
    # The main difficulty then becomes making sure that no two root
    #  intervals I_1 and I_2 overlap, even if I_1 and I_2 were
    #  contributed by different polynomials.  Currently, we take care
    #  of this in an utterly stupid way, by computing isolating
    #  intervals for the real roots of the product of all given
    #  univariate polys.  This works because the real_root_intervals()
    #  method guarantees that the isolating intervals computed for the
    #  roots of a single univariate polynomial are all disjoint.
    #
    # Note that Sage will take care to make the product polynomial
    #  square-free before its roots are isolated, so that the
    #  Bernstein/de Casteljau root isolation algorithm terminates.
    #  However, Sage must then be doing some computation to determine
    #  the multiplicity of each root within the (possibly
    #  non-square-free) original univariate product polynomial, as
    #  root multiplicities (with values possibly greater than one) are
    #  returned by the real_root_intervals() function.  The list of
    #  intervals it returns is a list of tuples of the form ((q_i,
    #  q_i'), m_i) s.t. m_i is the multiplicity of the root appearing
    #  in the interval ]q_i, q_i'[.  I'll need to look into this
    #  multiplicity determination, to see how we might disable it, as
    #  we don't care about root multiplicity in CAD.
    #
    #  Added some simple machinery for handling exact rational roots.
    #  This gets us (slightly) beyond the purely full-dimensional case.
    #

    def iso_root_intvls(self, polys):
        univ_polys = [p.univariate_polynomial() for p in polys]
        if (univ_polys==[]):
            return []
        else:
            easy_roots_global, rri = [], []
            prod = 1
            for p in univ_polys:
                easy_roots = p.roots()
                if easy_roots != []:
                    easy_roots_global += [[(a, a), m] for (a, m) in easy_roots]
                else:
                    prod = prod * p
            if prod != 1:
                rri = prod.real_root_intervals()
            #print "rri's: ", rri
            #print "easy_roots:", easy_roots_global
            return rri + easy_roots_global

    #
    # Given a rational interval (presented as (l, u), a lower and
    # upper bound, return k-many sample points inside of the interval,
    # selected `randomly,' if possible. (This is only impossible
    # when l=u, in which case we return the single point [l].)
    #

    def k_random_sps(self, l, u, k):
        if (l == u):
            return [l]
        else:
            out = []
            for x in range(k):
                out.append((RR(random.uniform(l, u))).exact_rational())
            return out

    #
    # Given a list isolating intervals for real roots of the form
    # [((q_i, q_i'), m_i)] (note that m_i is the multiplicity of the
    # root appearing in the interval ]q_i, q_i'[), compute a list of
    # sample points from every *sector* induced by the root intervals.
    # This amounts to selecting a rational sample point from intervals
    # *between* each root interval given.
    #
    # For instance, if we are given the root intervals:
    #
    #   [((-1, 1), 1), ((2, 3), 4)],
    #
    # then we'll want to compute sample points from intervals
    # *between* the real root intervals, i.e., we want sample points
    # from the following intervals which contain no roots:
    #
    #   ]-inf, -1[, ]1, 2[, ]3, +inf[.
    #
    # A valid list of sector sample points to return in this case
    # might be:
    #
    #   [-2, 3/2, 4].
    #
    # *num_sps is the number of sample points to select in each f.d. cell.
    #

    def sector_sps(self, root_intvls, num_sps=1, ambient_hyps=[], cur_var=None):
        if (root_intvls==[]):
            # Check to see if there is a constraint only in x[k] in
            # the ambient (non-goal) hyps, and try to satisfy it with
            # a single sample point. This is to help us avoid spurious
            # hyp relevance judgments over variables not contained in
            # the goal. Note: We consider only the first such hyp.
            if not(cur_var == None):
                relevant_hyps = filter((lambda h: h.poly == cur_var), ambient_hyps)
                if relevant_hyps != []:
                    #print "     >>> Making " + str(relevant_hyps[0]) + " True!"
                    h = relevant_hyps[0]
                    if h.op == "<":
                        return [-1]
                    elif h.op == ">":
                        return [1]
                    else:
                        return [0]
                else:
                    return [0]
            else:
                return [0]
        else:
            # Eliminate multiplicity and sort resulting intervals
            intvls = map((lambda (i, m): i), root_intvls)
            intvls.sort()
            # Compute f_q s.t. ]-inf, f_q[ is first sector approx.
            f_q = intvls[0][0]
            # Compute l_q s.t. ]l_q, +inf[ is last sector approx.
            l_q = intvls[len(intvls)-1][1]
            # Record outer sample points from f_q and l_q.
            # We make them integers to save bits!
            outer_sps = [floor(f_q - 1), ceil(l_q + 1)]
            # Compute a list of inner sector intervals. This is in a sense
            # a list of intervals `dual' to the isolating root intervals
            # in the list intvls above.
            inner_sector_intvls = []
            for i in range(len(intvls)-1):
                i1, i2 = intvls[i], intvls[i+1]
                r1 = i1[1]
                l2 = i2[0]
                inner_sector_intvls.append((r1, l2))
            # Compute a list of sample points from each inner sector interval
            inner_sps = map((lambda (l, r): self.k_random_sps(l, r, num_sps)), inner_sector_intvls)
            # Now that we're doing more than full-dim, let's also sample from root intervals:
            root_sps = map((lambda (l, r): self.k_random_sps(l, r, 1)), intvls)
            # inner_sps is now a list of lists; we need to flatten it:
            join = lambda it: (y for x in it for y in x)
            inner_sps_flat = list(join(inner_sps))
            root_sps_flat = list(join(root_sps))
            # Return a sorted list of all sector sample points
            sps = (outer_sps + inner_sps_flat + root_sps_flat)
            sps.sort()
            return sps

    #
    # Base phase for full-dimensional CAD: Compute a sample point in
    # each full-dimensional sector (i.e., region homeomorphic to R^1)
    # of a CAD of R^1 induced by the 0-level projection set
    # proj_sets[0], and store the result as the sorted list
    # self.cell_sps[0].  This will form the base of our cell tree.
    #
    # *num_sps is the number of sample points to select in each f.d. cell.
    #

    def base_phase(self, num_sps=1, ambient_hyps=[]):
        print "-- Base phase:"
        print "   Isolating root (section) intervals for base projection set"
        base_section_intvls = self.iso_root_intvls(self.proj_sets[0])
        print "       ... Done(" + str(len(base_section_intvls)) +")!"
        print "   Isolating sample points from full-dimensional cells (sectors)"
        base_sector_sps = self.sector_sps(base_section_intvls, \
                                          num_sps=num_sps, \
                                          ambient_hyps=ambient_hyps, \
                                          cur_var = self.proj_ord[0])
        print "       ... Done(" + str(len(base_sector_sps)) +")!"
        self.cell_sps[0] = base_sector_sps
        print (".:. " + str(len(base_sector_sps))
               + " base rational sample points now bound to self.cell_sps[0].")


    #
    # Stack construction: Given a cell (identified by a pair
    #  consisting of a level L and a left-to-right index I), construct
    #  a full-dimensional stack over it.
    #
    # This amounts to:
    #   (1) Substituting the sample point self.cell_sps[L][I] in for
    #       x_0 ... x_L in proj_sets[L+1], so as to obtain a
    #       univariate family of polynomials in Q[x_{L+1}] (and then
    #       applying projection filtering to them),
    #
    #   (2) Applying the sector_sps (sector sample point) machinery to
    #       the family computed in (1). Then, these sample points must
    #       be mapped over and translated into (L+1)-dimensional
    #       sample points by making their L-dimensional components
    #       equal to self.cell_sps[L+1][I].
    #
    # We return the constructed stack as a sorted list of
    # (L+1)-dimensional sample points, with no modification to self.
    #
    # Note that if atoms are given, then we do partial stack
    # construction: Given a cell (identified by a pair consisting of a
    # level L and a left-to-right index I) *and* a list of our input
    # (in)equality atoms, construct a full-dimensional stack over the
    # given cell only if we can't decide, by evaluation, our top-level
    # input formula to be invalid over the cell. I want to do this
    # using the logical machinery, but I need the ability to evaluate
    # formulas upon partial models, which we'll need to figure out how
    # to do. In the mean time, I just have a little homegrown evaluator
    # function!
    #

    def stack_over_cell(self, l, i, goal=None, num_sps=1, ambient_hyps=[]):
        stack_parent = self.cell_sps[l][i]
        next_proj_set = self.proj_sets[l+1]
        parent_dict = {}
        if (l==0): # Base (l==0) sample points are scalars, not lists
            parent_dict[self.proj_ord[0]] = stack_parent
        else: # All other level (l!=0) sample points are lists
            for u in range(l+1):
                parent_dict[self.proj_ord[u]] = stack_parent[u]
        # Now that we have the dictionary of parent sample points of
        # the cell we're lifting over, let's see if we can decide
        # any of our atoms by partial evaluation!
        # atoms_over_cell = [a.eval_on_dict(parent_dict) for a in atoms]
        # # If any member of atoms_over_cell is False, then we need not
        # # lift over this cell and can return the empty stack.
        # if atoms_over_cell.count(False) > 0:
        #     print "--> Partiality short-circuited lifting over cell (R^" \
        #         + str(l) + "):" + str(i) + "!"
        #     return []

        # Special partiality for GRF: We short-circuit True cells!

        if goal.eval_on_dict(parent_dict) == True:
            print "--> Partiality for GRF short-circuited lifting over cell (R^" \
                + str(l) + "):" + str(i) + "!"
            return []
        else:
            univ_family = self.filter_proj_set([p.substitute(parent_dict)
                                                for p in next_proj_set])
            root_intvls = self.iso_root_intvls(univ_family)
            stack_extension = self.sector_sps(root_intvls, \
                                              num_sps=num_sps, \
                                              ambient_hyps=ambient_hyps, \
                                              cur_var = self.proj_ord[l+1])
            if l == 0: # Base (l==0) sample points are scalars, not lists
                final_stack = [[stack_parent] + [c] for c in stack_extension]
            else: # All other level (l!=0) sample points are lists
                final_stack = [stack_parent + [c] for c in stack_extension]
                final_stack.sort()
            return final_stack

    #
    # Lift from dimension/level L to dimension/level L+1.  This
    # amounts to constructing a stack over every L-dimensional cell
    # and (sort) unioning the results.
    #
    # We update self.cell_sps[L+1] with the (sorted) union of all the
    # stacks.
    #

    def lift_level(self, l, goal=None, num_sps=1, ambient_hyps=[]):
        stack_union = []
        for i in range(len(self.cell_sps[l])):
            stack_union = stack_union + self.stack_over_cell(l, i, goal, num_sps=num_sps, ambient_hyps=ambient_hyps)
        stack_union.sort()
        return stack_union

    #
    # Given an n-dimensional sample point S (as an n-element list),
    # construct a substitution dictionary from S s.t.
    #   self.proj_ord[i] |-> S[i].
    #

    def sp_dict(self, s):
        d = {}
        for i in range(len(s)):
            d[self.proj_ord[i]] = s[i]
        return d

    #
    # Perform the lifting phase.  This assumes that the projection and
    # base phases have already completed. Note that unless
    # retain_lower==true, we dispose of lower-dimensional sample
    # points once we have lifted over their corresponding cells (as
    # these lower-dimensional sample points are then no longer needed
    # for solving the Ex RCF decision problem). This is to conserve
    # memory.
    #

    def lifting_phase(self, retain_lower=False, goal=None, num_sps=1, ambient_hyps=[]):
        print "-- Lifting phase:"
        for l in range(self.num_vars-1):
            print ("   Lifting from R^" + str(l+1) + " to R^" + str(l+2))
            self.cell_sps[l+1] = self.lift_level(l, \
                                                 goal, \
                                                 num_sps=num_sps, \
                                                 ambient_hyps=ambient_hyps)
            print "      ... Done(" + str(len(self.cell_sps[l+1])) +")!"
            if not(retain_lower):
                self.cell_sps[l] = None
        # Now, self.cell_sps[self.num_vars-1] has full-dimensional
        # sample points.  Let's build a list of substitution
        # dictionaries from them.
        print (".:. " + str(len(self.cell_sps[self.num_vars-1])) +
               " " + str(self.num_vars) + "-dimensional sample points isolated.")
        if self.num_vars > 1:
            final_dicts = [self.sp_dict(s) for s in self.cell_sps[self.num_vars-1]]
        else:
            final_dicts = [self.sp_dict([s]) for s in self.cell_sps[self.num_vars-1]]
        print ".:. Sample point substitution dictionaries in self.final_sp_dicts."
        self.final_sp_dicts = final_dicts

    #
    # Compute a projection ordering and bind it to self.proj_ord.
    # We use the polynomials in self.proj_sets[self.num_vars - 1]
    # to determine a variable ranking.
    # We return the list in reverse projection order, e.g.,
    # [x[2], x[1], x[3]] means ``project x[3], then x[1], then x[2].''
    #



    #
    # Compute the final list of self.num_vars-dimensional sample point
    # substitution dictionaries sufficient for deciding AND-OR
    # combinations of strict inequalities involving the installed
    # top-level polynomials (i.e., self.proj_sets[self.num_vars-1]).
    #

    def sample_pt_dicts(self, retain_lower=false, goal=None, ambient_hyps=[], num_sps=1):
        self.projection_phase()
        self.base_phase(ambient_hyps=ambient_hyps)
        self.lifting_phase(retain_lower, \
                           goal, \
                           num_sps=num_sps, \
                           ambient_hyps=ambient_hyps)
        return self.final_sp_dicts

#################################################################
# :::::::> End core full-dimensional Ex RCF CAD code <::::::::: #
#################################################################


#################################################################
#
# Goal-directed full-dimensional decisions.
#
#################################################################

class RCF_GD_Decide(RCF):
    def __init__(self, num_vars, num_sps=1):
        self.q = QE_Factory(num_vars)
        self.num_vars = num_vars
        self.hyps = []
        self.goal = None # We store the goal in positive form
        self.witness = {}
        self.status = None
        self.num_sps = num_sps

    def __str__(self):

        def hyp_str(self):
            o = []
            i = 0
            for h in self.hyps:
                o = o + ["  H" + str(i) + ": " + str(h)]
                i += 1
            return join(o, " \n")

        self.goal.num_antecedent_hyps = len(self.hyps)

        return ("\n" + hyp_str(self)
                + "\n|-----------------------------------------  \n"
                + str(self.goal))

    def assert_hyps(self, atom, *atoms):
        self.hyps += [atom]
        for a in atoms:
            self.hyps += [a]
        self.witness = None
        self.status = None

    def assert_goal(self, g):
        self.goal = RCF_Goal(main_goal = g)
        self.witness = None
        self.status = None

    # Generic entry point for sampling
    # EPZ
    def sample_points(self,dict,sampling_params = None):
        return lss.local_search_sampling(self, dict, sampling_params);
        #return self.k_sample_points_in_ball(dict,25,0.05)

    # Some helpers for local search sampling
    def get_all_hyp_atoms(self):
        return self.hyps + self.goal.goal_hyps

    def get_hidden_hyp_atoms(self):
        return self.hyps
         
    
    def get_goal(self):
        return self.goal.main_goal
   #
   # Note for Erik: k_sample_points_in_ball() is the main function
   # for uniform ball sampling. This is a good place to start for
   # exploring more sophisticated sampling techniques. 
   # 
   # Note that the polynomials in the goal are available via
   #      self.goal.goal_polys().
   # 
   # -Grant
   #

    def k_sample_points_in_ball(self, dict, k, epsilon):
        def perturbe_dict():
            new_d = {}
            for v in dict.iterkeys():
                new_d[v] = dict[v] + random.uniform(-epsilon, epsilon)
                #sys.stderr.write("Old: {0}, New: {1}\n".format(dict[v], new_d[v]))
            return new_d
        #random.seed()
        #sys.stderr.write("Using [{0},{1}]\n".format(k,epsilon))
        return [perturbe_dict() for i in range(k)]

    def promote_right(self, i):
        h = self.hyps[i]
        self.hyps = self.hyps[:i] + self.hyps[i+1:]
        self.goal.add_goal_hyp(h, use_gbs=True)
        print "-- H" + str(i) + " has been promoted right."

    def bad_subsets_on_dict(self, dict, k=10, epsilon=0.01):
        bads = []
        # Is the goal true on the dictionary?
        if self.goal.eval_on_dict(dict):
            #print (" - Goal sequent true on " + str(dict) + ".")
            return None
        else:
            print (" - Goal sequent false on " + str(dict) + ".")
            print (" - Computing " + str(k) + " additional sample points \
in a (uniform) epsilon(=" + str(epsilon) + ") neighborhood.")
            #all_pts = [dict] + self.k_sample_points_in_ball(dict, k, epsilon)
            all_pts = [dict] + self.sample_points(dict);
            #print " - New list of dictionaries for all sample points:"
            #print str(all_pts)
            sys.stdout.write(" - Evaluating hypotheses over sample points..."),
            c = 0
            for d in all_pts:
                #print ("   Sample point #" + str(c) + ":", str(d))
                #print('.')
                g_status = self.goal.eval_on_dict(d)
                if g_status:
                    None
                    #print ("   Skipping sample point -- It's in a non-bad cell!")
                else:
                    #print ("   Hypotheses on sample pt: ")
                    h = []
                    i = 0
                    bad = []
                    for a in self.hyps:
                        r = a.eval_on_dict(d)
                        #print ("    H" + str(i) + ": " + str(a) + " ... " + str(r))
                        h = h + [r]
                        if r:
                            bad = bad + [i]
                            # h is a vector of True and False in the order of self.hyps
                        i += 1
                    #print "    Hypothesis vector for this sample point:"
                    #print "    " + str(h)
                    #print "    *Powerset to rule out, generated by:"
                    #print "    " + str(bad)
                    if len(bad) == len(self.hyps):
                        raise Exception("Counterexample!: " + str(d))
                    if bad not in bads and bad != []:
                        # Filter out sets in bads that are subsets of
                        # bad. This is a disgusting hack! Must change
                        # to tuple representation soon.
                        bads = [list(b) for b in set([tuple(b) for b in bads])]
                        bads = filter((lambda s: not(set(s).issubset(set(bad)))), bads)
                        bads += [bad]
                c += 1
            sys.stdout.write("Done.\n")
            return bads

    def weight_hyps(self):
        out = []
        vars_in_goal = set([v for h in (self.goal.goal_hyps + [self.goal.main_goal]) \
                            for v in h.poly.variables()])
        for h in self.hyps:
            # If h consists only of variables not in the goal, then we want to give
            # it a very high weighting, to bias the system against it.
            h_vars = set(h.poly.variables())
            #print "vars_in_goal: ", vars_in_goal
            #print "h_vars: ", h_vars
            if len(h_vars.intersection(vars_in_goal)) == 0:
                #print "---> Weighting hyp " + str(h) + " heavily since it can't influence the current goal."
                out += [10000]
            else:
                # A simple weighting scheme - must experiment with others!
                out += [max(10*(h.poly.total_degree() - 1) + 100*(h.poly.nvariables() - 1), 1)]
        return out

#
# Redoing good_hyps to use Sage's GLPK, and not to call muse.py (Gurobi).
# G. Passmore, Last updated 15-Dec-2013.
#

    def good_hyps(self, bads):

        # --hyps=\"" +str(range(len(self.hyps)))+ "\"\
        # --bad_hyps=\"" + str(bads) +"\"\
        # --weights=\"" + str(self.weight_hyps()) 

        p = MixedIntegerLinearProgram(maximization=False)
        x = p.new_variable(binary=True)
        hyps = range(len(self.hyps))
        for b in bads:
            #print "Working on b = ", b
            b_c = filter((lambda h: h not in b), hyps)
            #print "b_c = ", b_c
            if (b_c == []):
                # Encode an inconsistency
                p.add_constraint(x[0] == 0)
                p.add_constraint(x[0] == 1)
                print
                print "*** Optimization problem is infeasible!"
                print "    Offending hyps list: ", b
                print
            else:
                e = sum([x[h] for h in b_c])
                p.add_constraint(e >= 1)
        w = self.weight_hyps()
        #print "Weights: ", w
        obj = sum([(w[h] * x[h]) for h in hyps])
        #print "Objective function: ", obj
        p.set_objective(obj)
        #print "Final optimization problem:"
        p.show()
        print "-- Solving minimal hypothesis subset 0-1 optimization problem:"
        p.solve()
        out = [i for i, v in p.get_values(x).iteritems() if v == 1]
        #print "Computed: ", out
        return out

    def check(self, partial=false, k=100, epsilon=2, interactive=False):
        #print ("* Selecting " + str(self.num_sps) + " sample points per cell.")
        if False: # This exception is now spurious - TODO: remove this branch
            raise Exception("spurious")
        else:
            self.q.install_polys(self.goal.main_goal.poly)
            for h in self.goal.goal_hyps:
                self.q.install_polys(h.poly)
            print "\n-- Beginning CAD on RHS of goal sequent."
            if partial:
                #print "Deciding using partial GRF CAD!"
                sp_dicts = self.q.sample_pt_dicts(goal=self.goal, \
                                                  num_sps=self.num_sps, \
                                                  ambient_hyps=self.hyps)
            else:
                sp_dicts = self.q.sample_pt_dicts(num_sps = self.num_sps, \
                                                  ambient_hyps=self.hyps)
            goal_sequent_true = True
            bads = []
            for sp_dict in sp_dicts:
                b = self.bad_subsets_on_dict(sp_dict, k=k, epsilon=epsilon)
                if (b != None):
                    goal_sequent_true = False
                    bads += b
            print "\n\n*** Goal sequent:", str(self)
            print "\n***"
            if goal_sequent_true:
                print "-- RHS of goal sequent is True, thus no bad subsets to rule out!"
                print "-- Final hypotheses to use:"
                print "  ", join([str(h) for h in self.goal.goal_hyps], ", ")
                print "-- Process completed.\n"
                return []
            else:
                if interactive:
                    i_done = False
                    while not(i_done):
                        i = raw_input("Enter ID of H to promote (0.." + str(len(self.hyps)-1) + \
                                      "), S for suggestion,\n      B to print bad H subsets, P to print sequent,\n      GO for auto finish> ")
                        i = i.lower()
                        if (i == 's'):
                            print "\n-- Computing suggested subset of {H0,...,H" + str(len(self.hyps)-1) + "}:"
                            cand = self.good_hyps(bads)
                            print "  ", cand
                            if len(cand) > 1:
                                print "-- Sorting suggested hypotheses by hypothesis weight:"
                                print "  ", sorted(cand, key=(lambda h:(self.hyps[h]).poly.total_degree())), "\n"
                            else:
                                print
                        elif (i == 'go'):
                            print ">> Entering auto mode."
                            print "-- Sorting candidates by hypothesis weight:"
                            cand = self.good_hyps(bads)
                            cand = sorted(cand, key=(lambda h:(self.hyps[h]).poly.total_degree()))
                            print "  ", cand
                            print "-- Promoting first hypothesis in sorted candidate subset."
                            self.promote_right(cand[0])
                            i_done = True
                            interactive = False
                        elif (i == 'b'):
                            print "\n-- Final bad subsets of {H0,...,H" + str(len(self.hyps)-1) + "} to rule out:"
                            print bads
                            print ""
                        elif (i == 'p'):
                            print "\n\n*** Goal sequent:", str(self)
                            print "\n***\n"
                        else:
                            try:
                                h = int(i)
                                if h in range(0, len(self.hyps)):
                                    self.promote_right(h)
                                    i_done = True
                            except ValueError:
                                print "*** Invalid input. Please try again."
                    self.check(interactive=interactive, partial=partial, k=k, epsilon=epsilon)
                else:
                    print "-- Computing a minimal candidate good subset of hypotheses:"
                    cand = self.good_hyps(bads)
                    if len(cand) > 1:
                        print "  ", cand
                        print "-- Sorting candidates by hypothesis weight:"
                        cand = sorted(cand, key=(lambda h:(self.hyps[h]).poly.total_degree()))
                        print "  ", cand
                        print "-- Promoting first hypothesis in sorted candidate subset."
                    else:
                        print "-- Promoting first (only) hypothesis in candidate subset."
                    self.promote_right(cand[0])
                    self.check(interactive=False, partial=partial, k=k, epsilon=epsilon)

                return bads

#################################################################
# :::::::> Begin tests <::::::::::::::::::::::::::::::::::::::: #
#################################################################

# load("/Users/grantp/Research/Sage/grant-goal-directed-rcf.sage")

def test_4d_1():
    d = RCF_Decide(4)
    q = d.q
    x0, x1, x2, x3 = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(x0*x3 + x1*x3 + x2*x1, "<", 0)
    a1 = RCF_Atom(x1, ">", 0)
    a2 = RCF_Atom(x2, ">", 0)
    a3 = RCF_Atom(x3, ">", 0)
    a4 = RCF_Atom(x2*x3 - x3**2 + x2**2 + 1, "<", 0)

    d.assert_atoms(a0, a1, a2, a3, a4)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness


def test_4d_2():
    d = RCF_Decide(4)
    q = d.q
    x0, x1, x2, x3 = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(x0*x3 + x1*x3 + x2*x1, "<", 0)
    a1 = RCF_Atom(x1, ">", x2)
    a2 = RCF_Atom(x2, ">", 0)
    a3 = RCF_Atom(x3, ">", 0)
    a4 = RCF_Atom(x2*x3 - x3**2 + x2**2 + 1, "<", 0)

    d.assert_atoms(a0, a1, a2, a3, a4)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

# A problem from: http://homepages.inf.ed.ac.uk/s0793114/calculemus09/qepcad/prob11.qepcad
def test_6d_1():
    d = RCF_Decide(6)
    q = d.q
    y, pa, pc, x, r, pb = q.x[0], q.x[1], q.x[2], q.x[3], q.x[4], q.x[5]

    a0 = RCF_Atom(x - pb*r, "<", 0)
    a1 = RCF_Atom(pc, ">", 0)
    a2 = RCF_Atom(pb, ">", 0)
    a3 = RCF_Atom(pa, ">", 0)
    a4 = RCF_Atom(pa*pc - r, ">", 0)
    a5 = RCF_Atom(x - pa*y, ">", 0)

    d.assert_atoms(a0, a1, a2, a3, a4, a5)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_6d_1_partial():
    d = RCF_Decide(6)
    q = d.q
    y, pa, pc, x, r, pb = q.x[0], q.x[1], q.x[2], q.x[3], q.x[4], q.x[5]

    a0 = RCF_Atom(x - pb*r, "<", 0)
    a1 = RCF_Atom(pc, ">", 0)
    a2 = RCF_Atom(pb, ">", 0)
    a3 = RCF_Atom(pa, ">", 0)
    a4 = RCF_Atom(pa*pc - r, ">", 0)
    a5 = RCF_Atom(x - pa*y, ">", 0)

    d.assert_atoms(a0, a1, a2, a3, a4, a5)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check(partial=true)
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_6d_2():
    d = RCF_Decide(6)
    q = d.q
    y, pa, pc, x, r, pb = q.x[0], q.x[1], q.x[2], q.x[3], q.x[4], q.x[5]

    a0 = RCF_Atom(x - pb*r, "<", 0)
    a1 = RCF_Atom(pc, ">", 0)
    a2 = RCF_Atom(pb, ">", 0)
    a3 = RCF_Atom(pa, ">", 0)
    a4 = RCF_Atom(pa*pc - r, "<", 0) # Swapped inequality from
                                    # test_6d_1; it then becomes SAT!
    a5 = RCF_Atom(x - pa*y, ">", 0)

    d.assert_atoms(a0, a1, a2, a3, a4, a5)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_6d_2_partial():
    d = RCF_Decide(6)
    q = d.q
    y, pa, pc, x, r, pb = q.x[0], q.x[1], q.x[2], q.x[3], q.x[4], q.x[5]

    a0 = RCF_Atom(x - pb*r, "<", 0)
    a1 = RCF_Atom(pc, ">", 0)
    a2 = RCF_Atom(pb, ">", 0)
    a3 = RCF_Atom(pa, ">", 0)
    a4 = RCF_Atom(pa*pc - r, "<", 0) # Swapped inequality from
                                    # test_6d_1; it then becomes SAT!
    a5 = RCF_Atom(x - pa*y, ">", 0)

    d.assert_atoms(a0, a1, a2, a3, a4, a5)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check(partial=true)
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness


def test_10d():
    d = RCF_Decide(10)
    q = d.q
    for i in range(10):
        d.assert_atoms(RCF_Atom(q.x[i], ">", 0))
    d.assert_atoms(RCF_Atom(q.x[0] - (q.x[1]*q.x[2] + q.x[3]), ">", 0))
    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_10d_partial():
    d = RCF_Decide(10)
    q = d.q
    for i in range(10):
        d.assert_atoms(RCF_Atom(q.x[i], ">", 0))
    d.assert_atoms(RCF_Atom(q.x[0] - (q.x[1]*q.x[2] + q.x[3]), ">", 0))
    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check(partial=true)
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness


def test_12d():
    d = RCF_Decide(12)
    q = d.q
    for i in range(12):
        d.assert_atoms(RCF_Atom(q.x[i], ">", 0))
    d.assert_atoms(RCF_Atom(q.x[0] - (q.x[1]*q.x[2] + q.x[3]), ">", 0))
    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_12d_partial():
    d = RCF_Decide(12)
    q = d.q
    for i in range(12):
        d.assert_atoms(RCF_Atom(q.x[i], ">", 0))
    d.assert_atoms(RCF_Atom(q.x[0] - (q.x[1]*q.x[2] + q.x[3]), ">", 0))
    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check(partial=true)
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness


def test_4d_q():
    d = RCF_Decide(4)
    q = d.q
    x, a, b, c = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(a*x**1000 + b**10*x + c, "<", 0)
    a1 = RCF_Atom(b**2 - 4*a*c, ">", 0)

    d.assert_atoms(a0, a1)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check()
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness

def test_4d_q_partial():
    d = RCF_Decide(4)
    q = d.q
    x, a, b, c = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(a*x**1000 + b**10*x + c, "<", 0)
    a1 = RCF_Atom(b**2 - 4*a*c, ">", 0)

    d.assert_atoms(a0, a1)

    print "-----"
    print "Asserted conjunction:"
    print d
    print "-----"
    print "Deciding the existential closure of this formula over the reals:"
    d.check(partial=true)
    print "-----"
    print "Final status:",
    print d.status
    if d.status:
        print "Witness:",
        print d.witness


def test_goal_1():
    d = RCF_GD_Decide(4)
    q = d.q
    x, a, b, c = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(a, ">", 0)
    a1 = RCF_Atom(b, ">", 0)
    a2 = RCF_Atom(c, ">", 0)
    a3 = RCF_Atom(x, ">", 0)
    g = RCF_Atom(a*b, ">", 0)

    d.assert_hyps(a0, a1, a2, a3)
    d.assert_goal(g)

    print "-----"
    print "Formula:"
    print d
    print "-----"
    print "Examining good/bad cell hyp/goal correlation:"
    d.check()
    print "-----"


def test_goal_2(k=100, epsilon=2, interactive=True):
    d = RCF_GD_Decide(4)
    q = d.q
    x, a, b, c = q.x[0], q.x[1], q.x[2], q.x[3]

    a0 = RCF_Atom(a, ">", 0)
    a1 = RCF_Atom(b, ">", 0)
    a2 = RCF_Atom(x, ">", 0)
    a3 = RCF_Atom(c*x + b, ">", 0)
    a4 = RCF_Atom(x*a, ">", 0)
    a5 = RCF_Atom(x*x + a*a*b + 7, ">", 0)
    a6 = RCF_Atom(x*x + a*a + 8, ">", 0)
    a7 = RCF_Atom(x*x + a*a + 9, ">", 0)
    a8 = RCF_Atom(x*x + a*a + a*x + b + 9, ">", 0)
    a9 = RCF_Atom(2*a*a*a + b*b*b + x, ">", 0)
    a10 = RCF_Atom(a*a*a*b*b*b + x*b*c*c + 1, ">", 0)
    a11 = RCF_Atom(x*x + a*a + 8, ">", 0)
    a12 = RCF_Atom((x*x + a*a + 8 + a^4*b^7 + x*b*c*c + x*x + a*a + 8)*(x*x + a*a + 8), ">", 0)
    a13 = RCF_Atom((x*x + a*a*b*c + 2*c - c*c*c*x + 1), ">", 0)
    g = RCF_Atom(a*b + x, ">", 0)

    d.assert_hyps(a5, a6, a7, a8, a0, a1, a2, a3, a4, a9, a10, a11, a12, a13)
    d.assert_goal(g)

    print "***Goal sequent:"
    print d
    print "***"
    print "Examining good/bad cell hyp/goal correlation:"
    d.check(interactive=interactive, k=k, epsilon=epsilon)
    print "-----"






def test_all():
    # These tests are deprecated -- See the tests in smt2.py.
    test_4d_1()
    test_4d_2()
    test_6d_1()
    test_6d_1_partial()
    test_6d_2()
    test_6d_2_partial()
    test_10d()
    test_10d_partial()
    test_12d()
    test_12d_partial()
    test_4d_q()
    test_4d_q_partial()


#################################################################
# :::::::> End tests <::::::::::::::::::::::::::::::::::::::::: #
#################################################################
