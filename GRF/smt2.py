#
# Parse Sphinx-generated RCF hiding problems (expressed in a variant
#  of SMTLib2 QF_NRA expressions).
# We import them as GRF/RCF geometric relevance filtering problems.
#
# Written by G.O.Passmore (grant.passmore@cl.cam.ac.uk)
#
# To use: First, install pyparsing:
#   For raw Python: sudo easy_install pyparsing
#   For Sage, it's already installed
#    (under matplotlib; see import statement below).
#
# For use with Sage, use the following import of pyparsing:
#  * Note: If you're using Sage with Python 3.x,
#          change pyparsing_py2 to pyparsing_py3 in the import below.
#

from matplotlib.pyparsing_py2 import Literal, Keyword, Word, OneOrMore, ZeroOrMore, \
    Forward, NotAny, delimitedList, Group, Optional, Combine, alphas, nums, \
    alphanums, printables, dblQuotedString, empty, ParseException, ParseResults, \
    MatchFirst, oneOf, GoToColumn, ParseResults, StringEnd, FollowedBy, \
    ParserElement, QuotedString

# ! Make sure that grf.py is loaded in Sage before this file !

#
# With pyparsing, the default sys recursion limit must be increased for
#   parsing w.r.t. even relatively small recursive grammars.
#

import sys
sys.setrecursionlimit(2 ** 20)

#
# SMTContext: This `logical context' class is our connection to GRF,
# and is manipulated by the ParseSMT class (defined shortly below).
#

class SMTContext:
    def __init__(self, k=25, epsilon=0.1, interactive=True):
        self.QEF = QE_Factory(num_vars=1) # We add ring vars (indts) on demand
        self.x = self.QEF.x # vars for polynomial ring: self.x[i]
        self.var_map = {} # map between SMT consts and ring vars
        self.antecedent = []
        self.succedent = []
        self.logic = "(undeclared)"
        self.info = {}
        self.polys = []
        self.status = None
        self.witness = None
        self.sp_dicts = [] # Final sample point dictionary
        self.cpu_time = None
        self.hiding_result = None
        self.k = k
        self.epsilon = epsilon
        self.interactive = interactive
        self.sequent_str = ""


    def get_ring_var(self, s):
        if s in self.var_map:
            return self.var_map[s]
        else:
            cur_ring_vars = len(self.x)
            if len(self.var_map) < cur_ring_vars:
                new_x = self.x[len(self.var_map)]
                #print "Class of new ring var ", str(new_x), " is: ", new_x.__class__.__name__
                self.var_map[s] = new_x
                return new_x
            else:
                #print "Extending polynomial ring by 1 indeterminate."
                self.QEF = QE_Factory(cur_ring_vars + 1)
                self.x = self.QEF.x
                self.var_map = dict([(k, self.QEF.R(self.var_map[k])) for k in self.var_map.keys()])
                if self.polys != []:
                    self.polys = [self.QEF.R(p) for p in self.polys]
                new_x = self.x[cur_ring_vars]
                self.var_map[s] = new_x
                return new_x

            # TODO: when ring changes, update all atoms to new ring via coercion!

    def add_antecedent(self, a):
        self.antecedent = a

    def add_succedent(self, a):
        self.succedent = a

    def set_logic(self, l):
        self.logic = l

    def set_info(self, k,v):
        self.info.update({k:v})

    def show(self):
        print "\n-------------------------------------------------------"
        print "Geometric Relevance Filtering Context"
        print "-------------------------------------------------------"
        print "Antecedent:", [str(a) for a in self.antecedent]
        print "Succedent:", [str(a) for a in self.succedent]
        print "Polys:", str(self.polys)
        print "Info: " + str(self.info)
        print "Status:", self.status
        print "Witness:", self.witness
        print "-------------------------------------------------------\n"

    def perform_grf(self, s, l, t):

        self.sequent_str = t[1] # Must record the sequent_str for Sphinx

        # Clear pyparsing ownership of the antecedent and succedent lists

        self.antecedent = [a for a in self.antecedent]
        self.succedent = [s for s in self.succedent]

        self.witness = None
        #print "Performing Geometric Relevance Filtering:"
        self.GRF = RCF_GD_Decide(len(self.x))
        self.GRF.q = self.QEF

        # Currently, we eliminate all equations through Groebner bases.
        # Eventually, we will support real algebraic numbers and won't
        # need to do this.

        # eqs = [p.poly for p in filter((lambda h: h.op == "="), self.antecedent)]
        # print "Extracted equations:"
        # print eqs
        # I = ideal(eqs)
        # B = I.groebner_basis()
        # print "GBasis: ", B
        # print "Adjusting hypotheses:"
        #for h in self.antecedent:
        #    if h.op != "=":
        #        h.quotient_ring_inject(B)

        if len(self.succedent) > 1:
            self.succedent.reverse()
            for h in self.succedent[1:]:
                h.negate()
                self.antecedent = self.antecedent + [h]

        self.GRF.goal = RCF_Goal(main_goal=self.succedent[0])
        #a.quotient_ring_inject(B) # Must extend to allow non-singleton

        # Now that we've injected equational data, we eliminate equations from hyps.
        #self.GRF.hyps = filter((lambda h: h.op != "="), self.antecedent)

        #print "Updating parent ring for hypotheses..."
        for h in self.antecedent:
            h.update_ring(self.GRF.q.R)

        self.GRF.hyps = self.antecedent

        print "-- Initial sequent:"

        print str(self.GRF)

        self.GRF.check(interactive=self.interactive, k=self.k, epsilon=self.epsilon, partial=True)

        # Now, get out list of unused (to be hidden) hypotheses

        hyps_to_hide = self.GRF.hyps

        # Let's figure out how to address these hyps in terms of the original
        # succedent and antecedent.

        hide_antecedent = []
        hide_succedent = []

        i = 0
        for h in self.antecedent:
            if h in hyps_to_hide:
                hide_antecedent += [i]
            i += 1

        #print "succedent:", ", ".join([str(s) for s in self.succedent])
        s = self.succedent
        s.reverse()

        i = 0
        for h in s:
            if h in hyps_to_hide:
                hide_succedent += [i]
            i += 1

        self.hiding_result = {'hide_antecedent' : hide_antecedent,
                              'hide_succedent'  : hide_succedent}

        return self

class ParseSMT():

    def __init__(self, context=None, k=25, epsilon=0.1, interactive=True):
        if context == None:
            self.context = SMTContext(k=k, epsilon=epsilon, interactive=interactive)
        else:
            self.context = context
        self.apcad = False

        def proc_declare_fun(s, l, t):
            f = t.asList()
            f_name = f[1]
            f_domain = f[2]
            f_codomain = f[3]
            # Currently, we only support the definition of real Skolem constants.
            if f_domain==[] and f_codomain=='Real':
                print "** Declared new function symbol:", f_name
                return self.context.get_ring_var(f_name)
            else:
                print "-------------------------------------------------------"
                print "Skipped function declaration (types unsupported)."
                print " Name: " + str(f_name)
                print " Domain: " + str(f_domain)
                print " Codomain: " + str(f_codomain)
                print "-------------------------------------------------------"

        def proc_antecedent(s, l, t):
            #print "** New antecedent added to context!"
            self.context.add_antecedent(t[1])

        def proc_succedent(s, l, t):
            #print "** New succedent added to context!"
            self.context.add_succedent(t[1])

        def proc_set_info(s, l, t):
            i = t.asList()
            i_k = i[1]
            i_v = i[2]
            self.context.set_info(i_k, i_v)

        def proc_set_logic(s, l, t):
            l = t.asList()
            self.context.set_logic(l[1])

        def proc_check_sat(s, l, t):
            print "** (check-sat) command issued!"
            self.context.check_sat(apcad=self.apcad)

        def proc_add(s, l, t):
            return (t[1] + t[2])

        def proc_mult(s, l, t):
            return (t[1] * t[2])

        def proc_sub(s, l, t):
            return (t[1] - t[2])

        def proc_unary_neg_fn(s,l,t):
            return (0 - t[1])

        def proc_div(s, l, t):
            return (t[1] / t[2])

        def proc_var_or_const(s, l, t):
            return self.context.get_ring_var(t[0])

        def proc_le(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], "<=", t[2])

        def proc_lt(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], "<", t[2])

        def proc_eq(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], "=", t[2])

        def proc_neq(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], "!=", t[2])

        def proc_gt(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], ">", t[2])

        def proc_ge(s, l, t):
            self.context.polys += [(t[1] - t[2])]
            return RCF_Atom(t[1], ">=", t[2])

        # SMT token literals

        lit_lpar, lit_rpar = Literal("(").suppress(), Literal(")").suppress()
        lit_dot = Literal(".")

        # SMT2 `literal' unary negation is "~" and can work on numerals,
        #   e.g. ~100   or   ~100.2.

        lit_unary_neg = Literal('~')

        # Literals for supported declarations

        lit_sequent = Literal('sequent')
        lit_antecedent = Literal('antecedent')
        lit_succedent = Literal('succedent')

        # Literals for supported SMT-theory function symbols

        lit_plus = Literal('+')
        lit_times = Literal('*')
        lit_minus = Literal('-')
        lit_div = Literal('/') # only between explicit numerals

        # Keywords for supported SMT-theory relation symbols

        kw_le = Keyword("<=")
        kw_eq = Keyword("=")
        kw_neq = Keyword("!=")
        kw_ge = Keyword(">=")
        kw_lt = Keyword("<")
        kw_gt = Keyword(">")

        # Auxiliary functions for parsing various kinds of numerals.
        # Note that rational numbers have to in general use the Fraction class.
        # We later `name' the numerals so that they're FOL expressions.

        def doNum(s,l,t):
            if t[0] == lit_unary_neg:
                return (-1 * t[1])
            else:
                return t[0]

        def asIntIfPossible(s):
            if s[-1:] == ".":
                return s[:-1]
            else:
                return s

        def doReal(s,l,t):
            if t[0] == "~":
                return (-1 * self.context.QEF.R(asIntIfPossible(t[1]))) # Cast constant as a polynomial in our ring!
            else:
                # print "Trying to deal with: " + str(t[0])
                # print "Class: " + str(t[0].__class__.__name__)
                return self.context.QEF.R(QQ(sage_eval(asIntIfPossible(t[0])))) # Ugh! Tricky Sage-required coercions for constants!

        nat = Word(nums)

        # SMT2 real numbers must contain a dot, and can end with a dot, e.g., '3.'
        # They're always interpreted as exact rational numbers.

        real = (Optional(lit_unary_neg) + Combine(nat + lit_dot + Optional(nat))).\
            setParseAction(doReal)

        # SMT2 `quoted symbols' are enclosed in |'s, e.g. | Hello, world! |
        # KeYmaera uses these regularly for encoding comments in SMT2 files.

        quoted_sym = QuotedString(quoteChar = '|', multiline=True)

        # Sphinx uses "xyz" for strings.

        str_sym = QuotedString(quoteChar = '"', multiline=True)

        var_or_const = Word(alphanums + "-._:").setParseAction(proc_var_or_const)
        atom = (Word(alphanums + "-._:") | quoted_sym)
        number = real.setParseAction(lambda s,l,t: doReal(s,l,t))
        term = Forward()

        # SMT2 function symbols we support:

        fn_div = (lit_lpar + lit_div + term + term + lit_rpar).\
            setParseAction(proc_div)
        fn_add = (lit_lpar + lit_plus + term + term + lit_rpar).\
            setParseAction(proc_add)
        fn_mult = (lit_lpar + lit_times + term + term + lit_rpar).\
            setParseAction(proc_mult)
        fn_sub = (lit_lpar + lit_minus + term + term + lit_rpar).\
            setParseAction(proc_sub)
        fn_neg = (lit_lpar + lit_minus + term + lit_rpar).\
            setParseAction(proc_unary_neg_fn)

        fn = fn_div | fn_add | fn_mult | fn_sub | fn_neg
        term << ( number | var_or_const | fn )

        # SMT2 relation symbols we support:

        rln_le = (lit_lpar + kw_le + term + term + lit_rpar).\
            setParseAction(proc_le)
        rln_lt = (lit_lpar + kw_lt + term + term + lit_rpar).\
            setParseAction(proc_lt)
        rln_eq = (lit_lpar + kw_eq + term + term + lit_rpar).\
            setParseAction(proc_eq)
        rln_neq = (lit_lpar + kw_neq + term + term + lit_rpar).\
            setParseAction(proc_neq)
        rln_gt = (lit_lpar + kw_gt + term + term + lit_rpar).\
            setParseAction(proc_gt)
        rln_ge = (lit_lpar + kw_ge + term + term + lit_rpar).\
            setParseAction(proc_ge)

        rln = rln_le | rln_lt | rln_neq | rln_eq | rln_ge | rln_gt

        # # SMT2 formulas we support:

        fml = Forward()
        # fml_and = (lit_lpar + kw_and + fml + fml + lit_rpar).\
        #     setParseAction(proc_and)
        # fml_or = (lit_lpar + kw_or + fml + fml + lit_rpar).\
        #     setParseAction(proc_or)
        # fml_not = (lit_lpar + kw_not + fml + lit_rpar).\
        #     setParseAction(proc_not)
        # fml_imp = (lit_lpar + kw_imp + fml + fml + lit_rpar).\
        #     setParseAction(proc_imp)

        # fml << ( rln | fml_and | fml_or | fml_not | fml_imp )
        fml << ( rln )
        self.fmls = ZeroOrMore(fml)

        # Sphinx declarations we support:

        cmd_antecedent = (lit_lpar + lit_antecedent + Group(self.fmls) + lit_rpar).\
                         setParseAction(proc_antecedent)
        cmd_succedent = (lit_lpar + lit_succedent + Group(self.fmls) + lit_rpar).\
                        setParseAction(proc_succedent)

        cmd = (lit_lpar + lit_sequent + str_sym + cmd_antecedent + cmd_succedent + lit_rpar).\
              setParseAction(self.context.perform_grf)
        self.cmds = ZeroOrMore(cmd)

    def fmlsTokenList(self, s):
        return self.fmls.parseString(s, parseAll=True).asList()

    def processCommands(self, s, context=None):
        if context == None:
            self.cmds.parseString(s, parseAll=True)
            return self.context
        else:
            old_context = self.context
            self.context = context
            self.cmds.parseString(s, parseAll=True)
            new_context = self.context
            self.context = old_context
            return new_context

    def clearContext(self):
        self.context = SMTContext()


#
# Run GRF on an Sphinx hiding problem input file and produce a hiding
# list as output.
#

def grf_on_file(filename=None, k=25, epsilon=0.1, interactive=True, outfile=None):

    if filename == None:
        raise Exception('Filename of Sphinx hiding problem must be given.')

    print "\n-- Performing GRF upon file " + filename + "."
    print "   Parameters: [k = " + str(k) + ", epsilon = " + str(epsilon) + \
                                ", interactive = " + str(interactive) + "].\n"

    f = open(filename, 'r')
    problem_str = f.read()
    f.close()

    P = ParseSMT(k=k, epsilon=epsilon, interactive=interactive)
    ctxt = P.processCommands(problem_str)
    hide_ant = ctxt.hiding_result['hide_antecedent']
    hide_suc = ctxt.hiding_result['hide_succedent']

    # Prepare a result string

    result = ("(\"" + ctxt.sequent_str + "\" " + \
              "(" + (" ".join(["hide_antecedent_" + str(i) for i in hide_ant])) + ") " + \
              "(" + (" ".join(["hide_succedent_" + str(i) for i in hide_suc])) + ")" + \
              ")")

    print "\n-- Hiding result:"

    print result

    if outfile != None:
        print "-- Writing hiding result to file " + str(outfile) + "."

        f = open(outfile, 'w')
        f.write(result)
        f.close()

    print "\n-- GRF run complete.\n\n"



#
# Tests
#

def tests():
    p = ParseSMT()
    # print [str(x) for x in p.fmlsTokenList("(>= 100.0 5.)")]
    # print [str(x) for x in p.fmlsTokenList("(= ~100.0 100.0)")]
    # print [str(x) for x in p.fmlsTokenList("(> x 0.)")]
    # c = (p.processCommands("(assert (> (+ x (/ ~1. 100.)) z))"))
    # c.show()
    # # ^^^ Alternatively, can do: p.context.show()
    # print [str(x) for x in p.fmlsTokenList("(> (+ x (* z (/ ~1. 100.))) z)")]

    ex_ant = "(antecedent (>= (- x_358 ox_6) 0.0) (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0))"

    ex_ant_2 = "(antecedent (>= (+ x_358 ox_6) 0.0))"

    ex_ant_3 = "(antecedent (>= x y))"

    ex_ant_4 = "(antecedent (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))))"

    ex_sequent = '(sequent "x_358 - ox_6 >= 0,  x_3 - ox_6 >= 0,     2 * b * (x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_358 ox_6) 0.0) (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- x_358 ox_6)) (* v_359 v_359))))'

    ex_sequent_2 = '(sequent "x_358 - ox_6 >= 0,  x_3 - ox_6 >= 0,     2 * b * (x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_358 ox_6) 0.0) (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- x_358 ox_6)) (* v_359 v_359))))'

    ex_sequent_3 = '(sequent "x_358 - ox_6 >= 0,  x_3 - ox_6 >= 0,     2 * b * (x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_358 ox_6) 0.0) (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (+ A b) 0.0)))'

    ex_sequent_4 = '(sequent "   2 * b * Abs_13  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_13  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_13) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_13) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3)))))))'

    ex_hiding_30 = '(sequent "   2 * b * Abs_23  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_314 <= ep,  v_290 >= 0,  t_314 >= 0,  v_290 = v_3 + a_8 * t_314,  -t_314 * (v_290 - a_8 / 2 * t_314) <= y_289 - y_3,  y_289 - y_3 <= t_314 * (v_290 - a_8 / 2 * t_314),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_23  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_314) ^ 2 + t_314 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_23) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_314 ep) (>= v_290 0.0) (>= t_314 0.0) (= v_290 (+ v_3 (* a_8 t_314))) (<= (* (- t_314) (- v_290 (* (/ a_8 2.0) t_314))) (- y_289 y_3)) (<= (- y_289 y_3) (* t_314 (- v_290 (* (/ a_8 2.0) t_314)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_23) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_314 t_314)) (* t_314 v_3)))))))'

    # Verified result via QepcadB!
    # (E x0)(E x1)(E x2)(E x3)(E x4)(E x5)(E x6)(E x7)[[x6 - x2 - x5 x7 = 0] /\ [x4 > 0] /\ [((0 - x0 x3 x4^2) - (x3^2 x4^2) - (2 x0 x2 x4) - (2 x2 x3 x4) + (2 x0 x1) - x2^2) > 0] /\ [((0 - x4) + x5) <= 0] /\ [x2 >= 0] /\ [x5 >= 0] /\ [x3 >= 0] /\ [x0 > 0] /\ [((0 - x0 x3 x5^2) - (x3^2 x5^2) - (2 x0 x2 x5) - (2 x2 x3 x5) + (2 x0 x1) - x2^2) <= 0]].

    # New result after improvements to GRF:
    # Verified result via QepcadB!
    #(E x0)(E x1)(E x2)(E x3)(E x4)(E x5)(E x6)(E x7)[[x4 > 0] /\ [((0 - x0 x3 x4^2) - (x3^2 x4^2) - (2 x0 x2 x4) - (2 x2 x3 x4) + (2 x0 x1) - x2^2) > 0] /\ [((0 - x4) + x5) <= 0] /\ [x2 >= 0] /\ [x5 >= 0] /\ [x3 >= 0] /\ [x0 > 0] /\ [((0 - x0 x3 x5^2) - (x3^2 x5^2) - (2 x0 x2 x5) - (2 x2 x3 x5) + (2 x0 x1) - x2^2) <= 0]].

    #Result:
# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
# |-----------------------------------------
#       [x4 > 0] /\
#       [x2 >= 0] /\
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x4 > 0], [x2 >= 0], [-x4 + x5 <= 0], [x5 >= 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
# -- Process completed.

# Futher improved result after dynamic variable reordering and biasing against var-irrelevant hypotheses (29-Oct-2013):
#
# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
#   H6: [x4 > 0]
# |-----------------------------------------
#       [x2 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x5 <= 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]
#
# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x2 >= 0], [x5 >= 0], [-x4 + x5 <= 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
# -- Process completed.
#
# Verified by QepcadB!
# (x0,x1,x2,x3,x4,x5,x6,x7)
#
#(E x0)(E x1)(E x2)(E x3)(E x4)(E x5)(E x6)(E x7)[[((0 - x0 x3 x4^2) - (x3^2 x4^2) - (2 x0 x2 x4) - (2 x2 x3 x4) + (2 x0 x1) - x2^2) > 0] /\ [((0 - x4) + x5) <= 0] /\ [x2 >= 0] /\ [x5 >= 0] /\ [x3 >= 0] /\ [x0 > 0] /\ [((0 - x0 x3 x5^2) - (x3^2 x5^2) - (2 x0 x2 x5) - (2 x2 x3 x5) + (2 x0 x1) - x2^2) <= 0]].

    ex_hiding_29 = '(sequent "   2 * b * -(y_3 - oy_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_314) ^ 2 + t_314 * v_3),  t_314 <= ep,  v_290 >= 0,  t_314 >= 0,  v_290 = v_3 + a_8 * t_314,  -t_314 * (v_290 - a_8 / 2 * t_314) <= y_289 - y_3,  y_289 - y_3 <= t_314 * (v_290 - a_8 / 2 * t_314),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_10 >= 0,  y_289 - oy_10 >= 0,  2 * b * -(y_289 - oy_10) >  (v_290) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- y_3 oy_10))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_314 t_314)) (* t_314 v_3))))) (<= t_314 ep) (>= v_290 0.0) (>= t_314 0.0) (= v_290 (+ v_3 (* a_8 t_314))) (<= (* (- t_314) (- v_290 (* (/ a_8 2.0) t_314))) (- y_289 y_3)) (<= (- y_289 y_3) (* t_314 (- v_290 (* (/ a_8 2.0) t_314)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_10) 0.0) (>= (- y_289 oy_10) 0.0) (> (* (* 2.0 b) (- (- y_289 oy_10))) (* v_290 v_290))))'

# Result for 29 (29-Oct-2013):

# *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 + x1 - x9 <= 0]
#   H2: [-x0 - x8 <= 0]
#   H3: [x3 >= 0]
#   H4: [x4 >= 0]
#   H5: [x6 > 0]
#   H6: [x1 - x2 < 0]
# |-----------------------------------------
#       [x0 > 0] /\
#       [-x2 + x9 < 0] /\
#       [-x5*x8 - x3 + x7 = 0] /\
#       [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x3*x5 - 2*x3*x4*x5 - 2*x0*x1 + 2*x0*x2 - x3^2 > 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-1/2*x3*x5 - 1/2*x5*x7 - x1 + x9 <= 0]
#         -->
#       [2*x0*x2 - x7^2 - 2*x0*x9 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x0 > 0], [-x2 + x9 < 0], [-x5*x8 - x3 + x7 = 0], [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x3*x5 - 2*x3*x4*x5 - 2*x0*x1 + 2*x0*x2 - x3^2 > 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-1/2*x3*x5 - 1/2*x5*x7 - x1 + x9 <= 0]
# -- Process completed.

    ex_hiding_28 = '(sequent "y_289 - oy_10 >= 0,     2 * b * -(y_3 - oy_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_314) ^ 2 + t_314 * v_3),  t_314 <= ep,  v_290 >= 0,  t_314 >= 0,  v_290 = v_3 + a_8 * t_314,  -t_314 * (v_290 - a_8 / 2 * t_314) <= y_289 - y_3,  y_289 - y_3 <= t_314 * (v_290 - a_8 / 2 * t_314),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_10 >= 0,  2 * b * (y_289 - oy_10) >  (v_290) ^ 2  " (antecedent (>= (- y_289 oy_10) 0.0) (> (* (* 2.0 b) (- (- y_3 oy_10))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_314 t_314)) (* t_314 v_3))))) (<= t_314 ep) (>= v_290 0.0) (>= t_314 0.0) (= v_290 (+ v_3 (* a_8 t_314))) (<= (* (- t_314) (- v_290 (* (/ a_8 2.0) t_314))) (- y_289 y_3)) (<= (- y_289 y_3) (* t_314 (- v_290 (* (/ a_8 2.0) t_314)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_10) 0.0) (> (* (* 2.0 b) (- y_289 oy_10)) (* v_290 v_290))))'

    ex_hiding_27 = '(sequent "y_3 - oy_10 >= 0,     2 * b * (y_3 - oy_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_314) ^ 2 + t_314 * v_3),  t_314 <= ep,  v_290 >= 0,  t_314 >= 0,  v_290 = v_3 + a_8 * t_314,  -t_314 * (v_290 - a_8 / 2 * t_314) <= y_289 - y_3,  y_289 - y_3 <= t_314 * (v_290 - a_8 / 2 * t_314),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_289 - oy_10 >= 0,  2 * b * -(y_289 - oy_10) >  (v_290) ^ 2  " (antecedent (>= (- y_3 oy_10) 0.0) (> (* (* 2.0 b) (- y_3 oy_10)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_314 t_314)) (* t_314 v_3))))) (<= t_314 ep) (>= v_290 0.0) (>= t_314 0.0) (= v_290 (+ v_3 (* a_8 t_314))) (<= (* (- t_314) (- v_290 (* (/ a_8 2.0) t_314))) (- y_289 y_3)) (<= (- y_289 y_3) (* t_314 (- v_290 (* (/ a_8 2.0) t_314)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_289 oy_10) 0.0) (> (* (* 2.0 b) (- (- y_289 oy_10))) (* v_290 v_290))))'

    ex_hiding_26 = '(sequent "y_289 - oy_10 >= 0,  y_3 - oy_10 >= 0,     2 * b * (y_3 - oy_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_314) ^ 2 + t_314 * v_3),  t_314 <= ep,  v_290 >= 0,  t_314 >= 0,  v_290 = v_3 + a_8 * t_314,  -t_314 * (v_290 - a_8 / 2 * t_314) <= y_289 - y_3,  y_289 - y_3 <= t_314 * (v_290 - a_8 / 2 * t_314),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (y_289 - oy_10) >  (v_290) ^ 2  " (antecedent (>= (- y_289 oy_10) 0.0) (>= (- y_3 oy_10) 0.0) (> (* (* 2.0 b) (- y_3 oy_10)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_314 t_314)) (* t_314 v_3))))) (<= t_314 ep) (>= v_290 0.0) (>= t_314 0.0) (= v_290 (+ v_3 (* a_8 t_314))) (<= (* (- t_314) (- v_290 (* (/ a_8 2.0) t_314))) (- y_289 y_3)) (<= (- y_289 y_3) (* t_314 (- v_290 (* (/ a_8 2.0) t_314)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- y_289 oy_10)) (* v_290 v_290))))'

# Result for 26 (as of 28-Oct-2013)!
#
# *** Goal sequent:
#   H0: [-x1 + x2 >= 0]
#   H1: [x6 - x7 <= 0]
#   H2: [1/2*x6^2*x9 - x6*x8 + x0 - x2 <= 0]
#   H3: [-x3 - x9 <= 0]
#   H4: [x4 >= 0]
#   H5: [x5 >= 0]
#   H6: [x7 > 0]
# |-----------------------------------------
#       [x0 - x1 >= 0] /\
#       [-x6*x9 - x4 + x8 = 0] /\
#       [-x3*x5*x6^2 - x5^2*x6^2 - 2*x3*x4*x6 - 2*x4*x5*x6 - 2*x1*x3 + 2*x2*x3 - x4^2 > 0] /\
#       [-x5 + x9 <= 0] /\
#       [x3 > 0] /\
#       [-1/2*x4*x6 - 1/2*x6*x8 - x0 + x2 <= 0] /\
#       [x8 >= 0] /\
#       [x6 >= 0]
#         -->
#       [2*x0*x3 - 2*x1*x3 - x8^2 > 0]
#
# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x0 - x1 >= 0], [-x6*x9 - x4 + x8 = 0], [-x3*x5*x6^2 - x5^2*x6^2 - 2*x3*x4*x6 - 2*x4*x5*x6 - 2*x1*x3 + 2*x2*x3 - x4^2 > 0], [-x5 + x9 <= 0], [x3 > 0], [-1/2*x4*x6 - 1/2*x6*x8 - x0 + x2 <= 0], [x8 >= 0], [x6 >= 0]
# -- Process completed.


    ex_hiding_25 = '(sequent "   2 * b * Abs_21  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_324 <= ep,  v_298 >= 0,  t_324 >= 0,  v_298 = v_3 + a_8 * t_324,  -t_324 * (v_298 - a_8 / 2 * t_324) <= x_297 - x_3,  x_297 - x_3 <= t_324 * (v_298 - a_8 / 2 * t_324),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_21  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_324) ^ 2 + t_324 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_21) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_324 ep) (>= v_298 0.0) (>= t_324 0.0) (= v_298 (+ v_3 (* a_8 t_324))) (<= (* (- t_324) (- v_298 (* (/ a_8 2.0) t_324))) (- x_297 x_3)) (<= (- x_297 x_3) (* t_324 (- v_298 (* (/ a_8 2.0) t_324)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_21) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_324 t_324)) (* t_324 v_3)))))))'

# Result for 25 (as of 28-Oct-2013)!
#
# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
# |-----------------------------------------
#       [x4 > 0] /\
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0] /\
#       [x2 >= 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]
#
# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x4 > 0], [-x4 + x5 <= 0], [x5 >= 0], [x2 >= 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
# -- Process completed.


    ex_hiding_24 = '(sequent "   2 * b * -(x_3 - ox_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_324) ^ 2 + t_324 * v_3),  t_324 <= ep,  v_298 >= 0,  t_324 >= 0,  v_298 = v_3 + a_8 * t_324,  -t_324 * (v_298 - a_8 / 2 * t_324) <= x_297 - x_3,  x_297 - x_3 <= t_324 * (v_298 - a_8 / 2 * t_324),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_10 >= 0,  x_297 - ox_10 >= 0,  2 * b * -(x_297 - ox_10) >  (v_298) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- x_3 ox_10))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_324 t_324)) (* t_324 v_3))))) (<= t_324 ep) (>= v_298 0.0) (>= t_324 0.0) (= v_298 (+ v_3 (* a_8 t_324))) (<= (* (- t_324) (- v_298 (* (/ a_8 2.0) t_324))) (- x_297 x_3)) (<= (- x_297 x_3) (* t_324 (- v_298 (* (/ a_8 2.0) t_324)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_10) 0.0) (>= (- x_297 ox_10) 0.0) (> (* (* 2.0 b) (- (- x_297 ox_10))) (* v_298 v_298))))'

    ex_hiding_23 = '(sequent "x_297 - ox_10 >= 0,     2 * b * -(x_3 - ox_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_324) ^ 2 + t_324 * v_3),  t_324 <= ep,  v_298 >= 0,  t_324 >= 0,  v_298 = v_3 + a_8 * t_324,  -t_324 * (v_298 - a_8 / 2 * t_324) <= x_297 - x_3,  x_297 - x_3 <= t_324 * (v_298 - a_8 / 2 * t_324),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_10 >= 0,  2 * b * (x_297 - ox_10) >  (v_298) ^ 2  " (antecedent (>= (- x_297 ox_10) 0.0) (> (* (* 2.0 b) (- (- x_3 ox_10))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_324 t_324)) (* t_324 v_3))))) (<= t_324 ep) (>= v_298 0.0) (>= t_324 0.0) (= v_298 (+ v_3 (* a_8 t_324))) (<= (* (- t_324) (- v_298 (* (/ a_8 2.0) t_324))) (- x_297 x_3)) (<= (- x_297 x_3) (* t_324 (- v_298 (* (/ a_8 2.0) t_324)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_10) 0.0) (> (* (* 2.0 b) (- x_297 ox_10)) (* v_298 v_298))))'

    ex_hiding_22 = '(sequent "x_3 - ox_10 >= 0,     2 * b * (x_3 - ox_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_324) ^ 2 + t_324 * v_3),  t_324 <= ep,  v_298 >= 0,  t_324 >= 0,  v_298 = v_3 + a_8 * t_324,  -t_324 * (v_298 - a_8 / 2 * t_324) <= x_297 - x_3,  x_297 - x_3 <= t_324 * (v_298 - a_8 / 2 * t_324),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_297 - ox_10 >= 0,  2 * b * -(x_297 - ox_10) >  (v_298) ^ 2  " (antecedent (>= (- x_3 ox_10) 0.0) (> (* (* 2.0 b) (- x_3 ox_10)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_324 t_324)) (* t_324 v_3))))) (<= t_324 ep) (>= v_298 0.0) (>= t_324 0.0) (= v_298 (+ v_3 (* a_8 t_324))) (<= (* (- t_324) (- v_298 (* (/ a_8 2.0) t_324))) (- x_297 x_3)) (<= (- x_297 x_3) (* t_324 (- v_298 (* (/ a_8 2.0) t_324)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_297 ox_10) 0.0) (> (* (* 2.0 b) (- (- x_297 ox_10))) (* v_298 v_298))))'

    ex_hiding_21 = '(sequent "x_297 - ox_10 >= 0,  x_3 - ox_10 >= 0,     2 * b * (x_3 - ox_10)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_324) ^ 2 + t_324 * v_3),  t_324 <= ep,  v_298 >= 0,  t_324 >= 0,  v_298 = v_3 + a_8 * t_324,  -t_324 * (v_298 - a_8 / 2 * t_324) <= x_297 - x_3,  x_297 - x_3 <= t_324 * (v_298 - a_8 / 2 * t_324),  -b <= a_8,  a_8 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_297 - ox_10) >  (v_298) ^ 2  " (antecedent (>= (- x_297 ox_10) 0.0) (>= (- x_3 ox_10) 0.0) (> (* (* 2.0 b) (- x_3 ox_10)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_324 t_324)) (* t_324 v_3))))) (<= t_324 ep) (>= v_298 0.0) (>= t_324 0.0) (= v_298 (+ v_3 (* a_8 t_324))) (<= (* (- t_324) (- v_298 (* (/ a_8 2.0) t_324))) (- x_297 x_3)) (<= (- x_297 x_3) (* t_324 (- v_298 (* (/ a_8 2.0) t_324)))) (<= (- b) a_8) (<= a_8 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- x_297 ox_10)) (* v_298 v_298))))'

    ex_hiding_20 = '(sequent "   2 * b * Abs_19  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_355 <= ep,  v_322 >= 0,  t_355 >= 0,  v_322 = v_3 + a_6 * t_355,  -t_355 * (v_322 - a_6 / 2 * t_355) <= y_321 - y_3,  y_321 - y_3 <= t_355 * (v_322 - a_6 / 2 * t_355),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_19  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_355) ^ 2 + t_355 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_19) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_355 ep) (>= v_322 0.0) (>= t_355 0.0) (= v_322 (+ v_3 (* a_6 t_355))) (<= (* (- t_355) (- v_322 (* (/ a_6 2.0) t_355))) (- y_321 y_3)) (<= (- y_321 y_3) (* t_355 (- v_322 (* (/ a_6 2.0) t_355)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_19) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_355 t_355)) (* t_355 v_3)))))))'

#     Result for 20:

# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
# |-----------------------------------------
#       [x4 > 0] /\
#       [x2 >= 0] /\
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x4 > 0], [x2 >= 0], [-x4 + x5 <= 0], [x5 >= 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
# -- Process completed.

    ex_hiding_19 = '(sequent "   2 * b * -(y_3 - oy_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_355) ^ 2 + t_355 * v_3),  t_355 <= ep,  v_322 >= 0,  t_355 >= 0,  v_322 = v_3 + a_6 * t_355,  -t_355 * (v_322 - a_6 / 2 * t_355) <= y_321 - y_3,  y_321 - y_3 <= t_355 * (v_322 - a_6 / 2 * t_355),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_8 >= 0,  y_321 - oy_8 >= 0,  2 * b * -(y_321 - oy_8) >  (v_322) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- y_3 oy_8))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_355 t_355)) (* t_355 v_3))))) (<= t_355 ep) (>= v_322 0.0) (>= t_355 0.0) (= v_322 (+ v_3 (* a_6 t_355))) (<= (* (- t_355) (- v_322 (* (/ a_6 2.0) t_355))) (- y_321 y_3)) (<= (- y_321 y_3) (* t_355 (- v_322 (* (/ a_6 2.0) t_355)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_8) 0.0) (>= (- y_321 oy_8) 0.0) (> (* (* 2.0 b) (- (- y_321 oy_8))) (* v_322 v_322)))'

    # We get a strange parse error on 19. Must investigate :-(.

    ex_hiding_18 = '(sequent "y_321 - oy_8 >= 0,     2 * b * -(y_3 - oy_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_355) ^ 2 + t_355 * v_3),  t_355 <= ep,  v_322 >= 0,  t_355 >= 0,  v_322 = v_3 + a_6 * t_355,  -t_355 * (v_322 - a_6 / 2 * t_355) <= y_321 - y_3,  y_321 - y_3 <= t_355 * (v_322 - a_6 / 2 * t_355),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_8 >= 0,  2 * b * (y_321 - oy_8) >  (v_322) ^ 2  " (antecedent (>= (- y_321 oy_8) 0.0) (> (* (* 2.0 b) (- (- y_3 oy_8))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_355 t_355)) (* t_355 v_3))))) (<= t_355 ep) (>= v_322 0.0) (>= t_355 0.0) (= v_322 (+ v_3 (* a_6 t_355))) (<= (* (- t_355) (- v_322 (* (/ a_6 2.0) t_355))) (- y_321 y_3)) (<= (- y_321 y_3) (* t_355 (- v_322 (* (/ a_6 2.0) t_355)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_8) 0.0) (> (* (* 2.0 b) (- y_321 oy_8)) (* v_322 v_322))))'

    ex_hiding_17 = '(sequent "y_3 - oy_8 >= 0,     2 * b * (y_3 - oy_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_355) ^ 2 + t_355 * v_3),  t_355 <= ep,  v_322 >= 0,  t_355 >= 0,  v_322 = v_3 + a_6 * t_355,  -t_355 * (v_322 - a_6 / 2 * t_355) <= y_321 - y_3,  y_321 - y_3 <= t_355 * (v_322 - a_6 / 2 * t_355),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  y_321 - oy_8 >= 0,  2 * b * -(y_321 - oy_8) >  (v_322) ^ 2  " (antecedent (>= (- y_3 oy_8) 0.0) (> (* (* 2.0 b) (- y_3 oy_8)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_355 t_355)) (* t_355 v_3))))) (<= t_355 ep) (>= v_322 0.0) (>= t_355 0.0) (= v_322 (+ v_3 (* a_6 t_355))) (<= (* (- t_355) (- v_322 (* (/ a_6 2.0) t_355))) (- y_321 y_3)) (<= (- y_321 y_3) (* t_355 (- v_322 (* (/ a_6 2.0) t_355)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_321 oy_8) 0.0) (> (* (* 2.0 b) (- (- y_321 oy_8))) (* v_322 v_322))))'

    ex_hiding_16 = '(sequent "y_321 - oy_8 >= 0,  y_3 - oy_8 >= 0,     2 * b * (y_3 - oy_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_355) ^ 2 + t_355 * v_3),  t_355 <= ep,  v_322 >= 0,  t_355 >= 0,  v_322 = v_3 + a_6 * t_355,  -t_355 * (v_322 - a_6 / 2 * t_355) <= y_321 - y_3,  y_321 - y_3 <= t_355 * (v_322 - a_6 / 2 * t_355),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (y_321 - oy_8) >  (v_322) ^ 2  " (antecedent (>= (- y_321 oy_8) 0.0) (>= (- y_3 oy_8) 0.0) (> (* (* 2.0 b) (- y_3 oy_8)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_355 t_355)) (* t_355 v_3))))) (<= t_355 ep) (>= v_322 0.0) (>= t_355 0.0) (= v_322 (+ v_3 (* a_6 t_355))) (<= (* (- t_355) (- v_322 (* (/ a_6 2.0) t_355))) (- y_321 y_3)) (<= (- y_321 y_3) (* t_355 (- v_322 (* (/ a_6 2.0) t_355)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- y_321 oy_8)) (* v_322 v_322))))'

    ex_hiding_15 = '(sequent "   2 * b * Abs_17  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_365 <= ep,  v_330 >= 0,  t_365 >= 0,  v_330 = v_3 + a_6 * t_365,  -t_365 * (v_330 - a_6 / 2 * t_365) <= x_329 - x_3,  x_329 - x_3 <= t_365 * (v_330 - a_6 / 2 * t_365),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_17  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_365) ^ 2 + t_365 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_17) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_365 ep) (>= v_330 0.0) (>= t_365 0.0) (= v_330 (+ v_3 (* a_6 t_365))) (<= (* (- t_365) (- v_330 (* (/ a_6 2.0) t_365))) (- x_329 x_3)) (<= (- x_329 x_3) (* t_365 (- v_330 (* (/ a_6 2.0) t_365)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_17) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_365 t_365)) (* t_365 v_3)))))))'

# Result for 15:

# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
#   H6: [x4 > 0]
# |-----------------------------------------
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0] /\
#       [x2 >= 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [-x4 + x5 <= 0], [x5 >= 0], [x2 >= 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0]
# -- Process completed.


    ex_hiding_14 = '(sequent "   2 * b * -(x_3 - ox_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_365) ^ 2 + t_365 * v_3),  t_365 <= ep,  v_330 >= 0,  t_365 >= 0,  v_330 = v_3 + a_6 * t_365,  -t_365 * (v_330 - a_6 / 2 * t_365) <= x_329 - x_3,  x_329 - x_3 <= t_365 * (v_330 - a_6 / 2 * t_365),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_8 >= 0,  x_329 - ox_8 >= 0,  2 * b * -(x_329 - ox_8) >  (v_330) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- x_3 ox_8))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_365 t_365)) (* t_365 v_3))))) (<= t_365 ep) (>= v_330 0.0) (>= t_365 0.0) (= v_330 (+ v_3 (* a_6 t_365))) (<= (* (- t_365) (- v_330 (* (/ a_6 2.0) t_365))) (- x_329 x_3)) (<= (- x_329 x_3) (* t_365 (- v_330 (* (/ a_6 2.0) t_365)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_8) 0.0) (>= (- x_329 ox_8) 0.0) (> (* (* 2.0 b) (- (- x_329 ox_8))) (* v_330 v_330))))'

    ex_hiding_13 = '(sequent "x_329 - ox_8 >= 0,     2 * b * -(x_3 - ox_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_365) ^ 2 + t_365 * v_3),  t_365 <= ep,  v_330 >= 0,  t_365 >= 0,  v_330 = v_3 + a_6 * t_365,  -t_365 * (v_330 - a_6 / 2 * t_365) <= x_329 - x_3,  x_329 - x_3 <= t_365 * (v_330 - a_6 / 2 * t_365),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_8 >= 0,  2 * b * (x_329 - ox_8) >  (v_330) ^ 2  " (antecedent (>= (- x_329 ox_8) 0.0) (> (* (* 2.0 b) (- (- x_3 ox_8))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_365 t_365)) (* t_365 v_3))))) (<= t_365 ep) (>= v_330 0.0) (>= t_365 0.0) (= v_330 (+ v_3 (* a_6 t_365))) (<= (* (- t_365) (- v_330 (* (/ a_6 2.0) t_365))) (- x_329 x_3)) (<= (- x_329 x_3) (* t_365 (- v_330 (* (/ a_6 2.0) t_365)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_8) 0.0) (> (* (* 2.0 b) (- x_329 ox_8)) (* v_330 v_330))))'

    ex_hiding_12 = '(sequent "x_3 - ox_8 >= 0,     2 * b * (x_3 - ox_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_365) ^ 2 + t_365 * v_3),  t_365 <= ep,  v_330 >= 0,  t_365 >= 0,  v_330 = v_3 + a_6 * t_365,  -t_365 * (v_330 - a_6 / 2 * t_365) <= x_329 - x_3,  x_329 - x_3 <= t_365 * (v_330 - a_6 / 2 * t_365),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  x_329 - ox_8 >= 0,  2 * b * -(x_329 - ox_8) >  (v_330) ^ 2  " (antecedent (>= (- x_3 ox_8) 0.0) (> (* (* 2.0 b) (- x_3 ox_8)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_365 t_365)) (* t_365 v_3))))) (<= t_365 ep) (>= v_330 0.0) (>= t_365 0.0) (= v_330 (+ v_3 (* a_6 t_365))) (<= (* (- t_365) (- v_330 (* (/ a_6 2.0) t_365))) (- x_329 x_3)) (<= (- x_329 x_3) (* t_365 (- v_330 (* (/ a_6 2.0) t_365)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_329 ox_8) 0.0) (> (* (* 2.0 b) (- (- x_329 ox_8))) (* v_330 v_330))))'

    ex_hiding_11 = '(sequent "x_329 - ox_8 >= 0,  x_3 - ox_8 >= 0,     2 * b * (x_3 - ox_8)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_365) ^ 2 + t_365 * v_3),  t_365 <= ep,  v_330 >= 0,  t_365 >= 0,  v_330 = v_3 + a_6 * t_365,  -t_365 * (v_330 - a_6 / 2 * t_365) <= x_329 - x_3,  x_329 - x_3 <= t_365 * (v_330 - a_6 / 2 * t_365),  -b <= a_6,  a_6 <= A,  v_3 >= 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_329 - ox_8) >  (v_330) ^ 2  " (antecedent (>= (- x_329 ox_8) 0.0) (>= (- x_3 ox_8) 0.0) (> (* (* 2.0 b) (- x_3 ox_8)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_365 t_365)) (* t_365 v_3))))) (<= t_365 ep) (>= v_330 0.0) (>= t_365 0.0) (= v_330 (+ v_3 (* a_6 t_365))) (<= (* (- t_365) (- v_330 (* (/ a_6 2.0) t_365))) (- x_329 x_3)) (<= (- x_329 x_3) (* t_365 (- v_330 (* (/ a_6 2.0) t_365)))) (<= (- b) a_6) (<= a_6 A) (>= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- x_329 ox_8)) (* v_330 v_330))))'

    ex_hiding_10 = '(sequent "   2 * b * Abs_15  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_393 <= ep,  v_351 >= 0,  t_393 >= 0,  v_351 = v_3 + a_4 * t_393,  -t_393 * (v_351 - a_4 / 2 * t_393) <= y_350 - y_3,  y_350 - y_3 <= t_393 * (v_351 - a_4 / 2 * t_393),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_15  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_393) ^ 2 + t_393 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_15) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_393 ep) (>= v_351 0.0) (>= t_393 0.0) (= v_351 (+ v_3 (* a_4 t_393))) (<= (* (- t_393) (- v_351 (* (/ a_4 2.0) t_393))) (- y_350 y_3)) (<= (- y_350 y_3) (* t_393 (- v_351 (* (/ a_4 2.0) t_393)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_15) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_393 t_393)) (* t_393 v_3)))))))'

# Result for 10:

# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
# |-----------------------------------------
#       [x2 = 0] /\
#       [x4 > 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0] /\
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x2 = 0], [x4 > 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 - 2*x0*x2*x4 - 2*x2*x3*x4 + 2*x0*x1 - x2^2 > 0], [-x4 + x5 <= 0], [x5 >= 0]
# -- Process completed.

    ex_hiding_9 = '(sequent "   2 * b * -(y_3 - oy_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_393) ^ 2 + t_393 * v_3),  t_393 <= ep,  v_351 >= 0,  t_393 >= 0,  v_351 = v_3 + a_4 * t_393,  -t_393 * (v_351 - a_4 / 2 * t_393) <= y_350 - y_3,  y_350 - y_3 <= t_393 * (v_351 - a_4 / 2 * t_393),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_6 >= 0,  y_350 - oy_6 >= 0,  2 * b * -(y_350 - oy_6) >  (v_351) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- y_3 oy_6))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_393 t_393)) (* t_393 v_3))))) (<= t_393 ep) (>= v_351 0.0) (>= t_393 0.0) (= v_351 (+ v_3 (* a_4 t_393))) (<= (* (- t_393) (- v_351 (* (/ a_4 2.0) t_393))) (- y_350 y_3)) (<= (- y_350 y_3) (* t_393 (- v_351 (* (/ a_4 2.0) t_393)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_6) 0.0) (>= (- y_350 oy_6) 0.0) (> (* (* 2.0 b) (- (- y_350 oy_6))) (* v_351 v_351))))'

#     Result for 9 (using GB reduction):

#     *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 + x1 - x9 <= 0]
#   H2: [-x0 - x8 <= 0]
#   H3: [x4 >= 0]
# |-----------------------------------------
#       [x3 = 0] /\
#       [x6 > 0] /\
#       [x1 - x2 < 0] /\
#       [x0 > 0] /\
#       [-x2 + x9 < 0] /\
#       [-x5*x8 + x7 = 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0] /\
#       [-1/2*x5*x7 - x1 + x9 <= 0]
#         -->
#       [2*x0*x2 - x7^2 - 2*x0*x9 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x3 = 0], [x6 > 0], [x1 - x2 < 0], [x0 > 0], [-x2 + x9 < 0], [-x5*x8 + x7 = 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0], [-1/2*x5*x7 - x1 + x9 <= 0]
# -- Process completed.
#
#
#   New result for 9 after dynamic variable reordering:
# *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 + x1 - x9 <= 0]
#   H2: [-x0 - x8 <= 0]
#   H3: [x4 >= 0]
#   H4: [x6 > 0]
#   H5: [x1 - x2 < 0]
# |-----------------------------------------
#       [x3 = 0] /\
#       [x0 > 0] /\
#       [-x2 + x9 < 0] /\
#       [-x5*x8 + x7 = 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0] /\
#       [-1/2*x5*x7 - x1 + x9 <= 0]
#         -->
#       [2*x0*x2 - x7^2 - 2*x0*x9 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x3 = 0], [x0 > 0], [-x2 + x9 < 0], [-x5*x8 + x7 = 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0], [-1/2*x5*x7 - x1 + x9 <= 0]
# -- Process completed.



    ex_hiding_8 = '(sequent "y_350 - oy_6 >= 0,     2 * b * -(y_3 - oy_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_393) ^ 2 + t_393 * v_3),  t_393 <= ep,  v_351 >= 0,  t_393 >= 0,  v_351 = v_3 + a_4 * t_393,  -t_393 * (v_351 - a_4 / 2 * t_393) <= y_350 - y_3,  y_350 - y_3 <= t_393 * (v_351 - a_4 / 2 * t_393),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  y_3 - oy_6 >= 0,  2 * b * (y_350 - oy_6) >  (v_351) ^ 2  " (antecedent (>= (- y_350 oy_6) 0.0) (> (* (* 2.0 b) (- (- y_3 oy_6))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_393 t_393)) (* t_393 v_3))))) (<= t_393 ep) (>= v_351 0.0) (>= t_393 0.0) (= v_351 (+ v_3 (* a_4 t_393))) (<= (* (- t_393) (- v_351 (* (/ a_4 2.0) t_393))) (- y_350 y_3)) (<= (- y_350 y_3) (* t_393 (- v_351 (* (/ a_4 2.0) t_393)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_3 oy_6) 0.0) (> (* (* 2.0 b) (- y_350 oy_6)) (* v_351 v_351))))'



    ex_hiding_7 = '(sequent "y_3 - oy_6 >= 0,     2 * b * (y_3 - oy_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_393) ^ 2 + t_393 * v_3),  t_393 <= ep,  v_351 >= 0,  t_393 >= 0,  v_351 = v_3 + a_4 * t_393,  -t_393 * (v_351 - a_4 / 2 * t_393) <= y_350 - y_3,  y_350 - y_3 <= t_393 * (v_351 - a_4 / 2 * t_393),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  y_350 - oy_6 >= 0,  2 * b * -(y_350 - oy_6) >  (v_351) ^ 2  " (antecedent (>= (- y_3 oy_6) 0.0) (> (* (* 2.0 b) (- y_3 oy_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_393 t_393)) (* t_393 v_3))))) (<= t_393 ep) (>= v_351 0.0) (>= t_393 0.0) (= v_351 (+ v_3 (* a_4 t_393))) (<= (* (- t_393) (- v_351 (* (/ a_4 2.0) t_393))) (- y_350 y_3)) (<= (- y_350 y_3) (* t_393 (- v_351 (* (/ a_4 2.0) t_393)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- y_350 oy_6) 0.0) (> (* (* 2.0 b) (- (- y_350 oy_6))) (* v_351 v_351))))'

# Result for 7 after dynamic variable reorderding (we couldn't solve before)!

# *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 - x0 + x9 <= 0]
#   H2: [-x2 - x8 <= 0]
#   H3: [x4 >= 0]
#   H4: [x6 > 0]
# |-----------------------------------------
#       [x3 = 0] /\
#       [x2 > 0] /\
#       [-x1 + x9 < 0] /\
#       [x0 - x1 >= 0] /\
#       [-x5*x8 + x7 = 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-x2*x4*x5^2 - x4^2*x5^2 + 2*x0*x2 - 2*x1*x2 > 0] /\
#       [-1/2*x5*x7 + x0 - x9 <= 0]
#         -->
#       [2*x1*x2 - x7^2 - 2*x2*x9 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x3 = 0], [x2 > 0], [-x1 + x9 < 0], [x0 - x1 >= 0], [-x5*x8 + x7 = 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-x2*x4*x5^2 - x4^2*x5^2 + 2*x0*x2 - 2*x1*x2 > 0], [-1/2*x5*x7 + x0 - x9 <= 0]
# -- Process completed.


    ex_hiding_6 = '(sequent "y_350 - oy_6 >= 0,  y_3 - oy_6 >= 0,     2 * b * (y_3 - oy_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_393) ^ 2 + t_393 * v_3),  t_393 <= ep,  v_351 >= 0,  t_393 >= 0,  v_351 = v_3 + a_4 * t_393,  -t_393 * (v_351 - a_4 / 2 * t_393) <= y_350 - y_3,  y_350 - y_3 <= t_393 * (v_351 - a_4 / 2 * t_393),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (y_350 - oy_6) >  (v_351) ^ 2  " (antecedent (>= (- y_350 oy_6) 0.0) (>= (- y_3 oy_6) 0.0) (> (* (* 2.0 b) (- y_3 oy_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_393 t_393)) (* t_393 v_3))))) (<= t_393 ep) (>= v_351 0.0) (>= t_393 0.0) (= v_351 (+ v_3 (* a_4 t_393))) (<= (* (- t_393) (- v_351 (* (/ a_4 2.0) t_393))) (- y_350 y_3)) (<= (- y_350 y_3) (* t_393 (- v_351 (* (/ a_4 2.0) t_393)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- y_350 oy_6)) (* v_351 v_351))))'

    ex_hiding_5 = '(sequent "   2 * b * Abs_13  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (ep) ^ 2 + ep * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>     2 * b * Abs_13  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3)  " (antecedent (> (* (* 2.0 b) Abs_13) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* ep ep)) (* ep v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) Abs_13) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3)))))))'

# Result for 5:

# *** Goal sequent:
#   H0: [x6 >= 0]
#   H1: [-x5*x7 - x2 + x6 = 0]
#   H2: [1/2*x5^2*x7 - x5*x6 - x8 + x9 <= 0]
#   H3: [1/2*x5^2*x7 - x5*x6 + x8 - x9 <= 0]
#   H4: [-x0 - x7 <= 0]
#   H5: [-x3 + x7 <= 0]
# |-----------------------------------------
#       [x2 = 0] /\
#       [x4 > 0] /\
#       [x3 >= 0] /\
#       [x0 > 0] /\
#       [-x0*x3*x4^2 - x3^2*x4^2 + 2*x0*x1 > 0] /\
#       [-x4 + x5 <= 0] /\
#       [x5 >= 0]
#         -->
#       [-x0*x3*x5^2 - x3^2*x5^2 - 2*x0*x2*x5 - 2*x2*x3*x5 + 2*x0*x1 - x2^2 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x2 = 0], [x4 > 0], [x3 >= 0], [x0 > 0], [-x0*x3*x4^2 - x3^2*x4^2 + 2*x0*x1 > 0], [-x4 + x5 <= 0], [x5 >= 0]
# -- Process completed.

    ex_hiding_4 = '(sequent "   2 * b * -(x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_6 >= 0,  x_358 - ox_6 >= 0,  2 * b * -(x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (> (* (* 2.0 b) (- (- x_3 ox_6))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_6) 0.0) (>= (- x_358 ox_6) 0.0) (> (* (* 2.0 b) (- (- x_358 ox_6))) (* v_359 v_359))))'

# Result for 4:

# *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 + x1 - x9 <= 0]
#   H2: [-x0 - x8 <= 0]
#   H3: [x4 >= 0]
# |-----------------------------------------
#       [x3 = 0] /\
#       [x6 > 0] /\
#       [x1 - x2 < 0] /\
#       [x0 > 0] /\
#       [-x2 + x9 < 0] /\
#       [-x5*x8 + x7 = 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0] /\
#       [-1/2*x5*x7 - x1 + x9 <= 0]
#         -->
#       [2*x0*x2 - x7^2 - 2*x0*x9 > 0]

# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x3 = 0], [x6 > 0], [x1 - x2 < 0], [x0 > 0], [-x2 + x9 < 0], [-x5*x8 + x7 = 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-x0*x4*x5^2 - x4^2*x5^2 - 2*x0*x1 + 2*x0*x2 > 0], [-1/2*x5*x7 - x1 + x9 <= 0]
# -- Process completed.


    ex_hiding_3 = '(sequent "x_358 - ox_6 >= 0,     2 * b * -(x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  x_3 - ox_6 >= 0,  2 * b * (x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_358 ox_6) 0.0) (> (* (* 2.0 b) (- (- x_3 ox_6))) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_358 ox_6)) (* v_359 v_359))))'

    ex_hiding_2 = '(sequent "x_3 - ox_6 >= 0,     2 * b * (x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  x_358 - ox_6 >= 0,  2 * b * -(x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (>= (- x_358 ox_6) 0.0) (> (* (* 2.0 b) (- (- x_358 ox_6))) (* v_359 v_359))))'

# Result for 2, after dynamic variable reordering and biasing against irrelevant hyps:
#
# *** Goal sequent:
#   H0: [x5 - x6 <= 0]
#   H1: [1/2*x5^2*x8 - x5*x7 - x0 + x9 <= 0]
#   H2: [-x2 - x8 <= 0]
#   H3: [x4 >= 0]
#   H4: [x6 > 0]
# |-----------------------------------------
#       [x2 > 0] /\
#       [-x1 + x9 < 0] /\
#       [-x5*x8 + x7 = 0] /\
#       [x3 = 0] /\
#       [x0 - x1 >= 0] /\
#       [x7 >= 0] /\
#       [x5 >= 0] /\
#       [-x4 + x8 <= 0] /\
#       [-x2*x4*x5^2 - x4^2*x5^2 + 2*x0*x2 - 2*x1*x2 > 0] /\
#       [-1/2*x5*x7 + x0 - x9 <= 0]
#         -->
#       [2*x1*x2 - x7^2 - 2*x2*x9 > 0]
#
# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [x2 > 0], [-x1 + x9 < 0], [-x5*x8 + x7 = 0], [x3 = 0], [x0 - x1 >= 0], [x7 >= 0], [x5 >= 0], [-x4 + x8 <= 0], [-x2*x4*x5^2 - x4^2*x5^2 + 2*x0*x2 - 2*x1*x2 > 0], [-1/2*x5*x7 + x0 - x9 <= 0]
# -- Process completed.


    ex_hiding_1 = '(sequent "x_358 - ox_6 >= 0,  x_3 - ox_6 >= 0,     2 * b * (x_3 - ox_6)  >    (v_3) ^ 2     + 2 * (A + b) * (A / 2 * (t_403) ^ 2 + t_403 * v_3),  t_403 <= ep,  v_359 >= 0,  t_403 >= 0,  v_359 = v_3 + a_4 * t_403,  -t_403 * (v_359 - a_4 / 2 * t_403) <= x_358 - x_3,  x_358 - x_3 <= t_403 * (v_359 - a_4 / 2 * t_403),  -b <= a_4,  a_4 <= A,  v_3 = 0,  A >= 0,  b >  0,  ep >  0 ==>  2 * b * (x_358 - ox_6) >  (v_359) ^ 2  " (antecedent (>= (- x_358 ox_6) 0.0) (>= (- x_3 ox_6) 0.0) (> (* (* 2.0 b) (- x_3 ox_6)) (+ (* v_3 v_3) (* (* 2.0 (+ A b)) (+ (* (/ A 2.0) (* t_403 t_403)) (* t_403 v_3))))) (<= t_403 ep) (>= v_359 0.0) (>= t_403 0.0) (= v_359 (+ v_3 (* a_4 t_403))) (<= (* (- t_403) (- v_359 (* (/ a_4 2.0) t_403))) (- x_358 x_3)) (<= (- x_358 x_3) (* t_403 (- v_359 (* (/ a_4 2.0) t_403)))) (<= (- b) a_4) (<= a_4 A) (= v_3 0.0) (>= A 0.0) (> b 0.0) (> ep 0.0)) (succedent (> (* (* 2.0 b) (- x_358 ox_6)) (* v_359 v_359))))'

# Result for 1, after dynamic variable reordering and biasing against irrelevant hyps:
#
# *** Goal sequent:
#   H0: [x0 - x1 >= 0]
#   H1: [-x1 + x2 >= 0]
#   H2: [x6 - x7 <= 0]
#   H3: [1/2*x6^2*x9 - x6*x8 + x0 - x2 <= 0]
#   H4: [-x3 - x9 <= 0]
#   H5: [x4 = 0]
#   H6: [x5 >= 0]
#   H7: [x7 > 0]
# |-----------------------------------------
#       [-x6*x9 - x4 + x8 = 0] /\
#       [-x3*x5*x6^2 - x5^2*x6^2 - 2*x3*x4*x6 - 2*x4*x5*x6 - 2*x1*x3 + 2*x2*x3 - x4^2 > 0] /\
#       [x3 > 0] /\
#       [-1/2*x4*x6 - 1/2*x6*x8 - x0 + x2 <= 0] /\
#       [x8 >= 0] /\
#       [x6 >= 0] /\
#       [-x5 + x9 <= 0]
#         -->
#       [2*x0*x3 - 2*x1*x3 - x8^2 > 0]
#
# ***
# -- RHS of goal sequent is True, thus no bad subsets to rule out!
# -- Final hypotheses to use:
#    [-x6*x9 - x4 + x8 = 0], [-x3*x5*x6^2 - x5^2*x6^2 - 2*x3*x4*x6 - 2*x4*x5*x6 - 2*x1*x3 + 2*x2*x3 - x4^2 > 0], [x3 > 0], [-1/2*x4*x6 - 1/2*x6*x8 - x0 + x2 <= 0], [x8 >= 0], [x6 >= 0], [-x5 + x9 <= 0]
# -- Process completed.


    P = ParseSMT()
    print "\n\n-- Below should be an empty context."
    P.context.show()
    ctxt = P.processCommands(ex_hiding_1)
    print "\n\n-- Below should be a non-empty context."
    ctxt.show()
    print "\n\n-- Hiding result:"
    print ctxt.hiding_result

    P.clearContext()
    print
