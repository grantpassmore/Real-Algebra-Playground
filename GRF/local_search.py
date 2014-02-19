import math
import numpy as np
import scipy.optimize as sp_opt
import warnings
import random

import sys

from sage.numerical.optimize import minimize as symb_min

warnings.filterwarnings('ignore', 'The iteration is not making good progress')

"""
Helper functions
"""

# The sorely needed sign function
# EPZ
def sign(x):
    if x == 0:
        return 0
    return math.copysign(1,x)

# Soft "zero" sampling routine
# F should be a list of floats,
# Sampling is biased towards small values
# EPZ
def softzero_sample(F):
    expF = [math.exp(-abs(f)) for f in F]
    Z = sum(expF)
    P = [p / Z for p in expF]
    print "Softmin dist:", P
    r = random.random()
    for i in xrange(len(F)):
        if r > P[i]:
            r = r - P[i]
        else:
            return i
    return max(0,len(F)-1)

# A simple class to make sure our mappings to and from dicts
# are consistent
class VarOrder:
    order = None
    @staticmethod
    def var_order(D):
        if not VarOrder.order:
            VarOrder.order = D.keys()
        return VarOrder.order
    @staticmethod
    def dict2vect(D):
        order = VarOrder.var_order(D)
        return [D[i] for i in order]
    @staticmethod
    def vect2dict(v):
        assert(VarOrder.order)
        N = len(v)
        assert(N == len(VarOrder.order))
        new_D = {}
        for i in range(N):
            key = VarOrder.order[i]
            new_D[key] = v[i]
        return new_D

# Functions for perturbing vectors and dicts
def perturb(x,e):
    N = len(x)
    return [x[i] + random.uniform(-e,e) \
                for i in xrange(N)]

def perturb_dict(D,e):
    new_D = {}
    for k in D.iterkeys():
        new_D[k] = D[k] + random.uniform(-e,e)
    return new_D

# Evaluate point D on atom list A
def truth_sig(Prob,D):
    A = Prob.get_all_hyp_atoms()
    return tuple([a.eval_on_dict(D) for a in A])  

# Select a hypothesis based on the "soft-zero" of their values
def choose_atom_softzero(Prob,x):
    D = VarOrder.vect2dict(x)
    Atoms = Prob.get_all_hyp_atoms()
    A_values = [a.poly.substitute(D) for a in Atoms]
    s = softzero_sample(A_values)
    return Atoms[s]

def choose_atom_random(Prob,x):
    Atoms = Prob.get_hidden_hyp_atoms()
    return random.choice(Atoms)

def choose_atom_true(Prob,x):
    D = VarOrder.vect2dict(x)
    Atoms = Prob.get_hidden_hyp_atoms() # Just the hidden hypotheses
    NeedFlip = filter(lambda x: x.eval_on_dict(D), Atoms) 

    # hypothesis that happen to be true on the set
    if len(NeedFlip) == 0:
        return None
    A = random.choice(NeedFlip)
    return A

def eval_poly(Poly,x):
    D = VarOrder.vect2dict(x)
    return Poly.substitute(D)

# Sets the function so root finding falsifies the atom
# Input: an RCF atom
def get_num_falsifying_func(A,x):
    N = len(x)
    flip_eps = 0
    if (A.op in ["<", "<="]):
        # Solve for P(x) - e = 0, so P(x) > 0
        flip_eps = -ineq_eps
    elif (A.op in [">", ">="]):
        # Solve for P(x) + e = 0, so P(x) < 0
        flip_eps = ineq_eps
    else:
        flip_eps = ineq_eps*random.choice([-1,0,1])
    # NB: stupid padding so it is an N*N system
    return lambda x: [eval_poly(A.poly,x) + flip_eps] + [0]*(N-1) 
            
# Sets the function so root finding flips the sign of the polynomial
# Input: RCF_Atom
def get_num_flipping_func(A,x, margin):
    N = len(x)
    p_val = eval_poly(A.poly,x)
    flip_eps = 0
    if p_val != 0:
        # If P(x) > 0, then solving for P(x') + e = 0 
        #   implies that P(x) < 0
        # Else P(x) < 0, so solving for P(x') - e = 0 
        #   implies that P(x) > 0
        flip_eps = math.copysign(margin,p_val)
    else:
        flip_eps = margin*random.choice([-1,1])
    # NB: stupid padding so it is an N*N system
    return lambda x: [eval_poly(A.poly,x) + flip_eps] + [0]*(N-1) 

def get_symb_flipping_func(A,x,margin):
    p_val = eval_poly(A.poly,x)
    flip_eps = 0
    if p_val != 0:
        flip_eps = math.copysign(margin,p_val)
    else:
        flip_eps = margin*random.choice([-1,1])
    return (A.poly + flip_eps)**2 

# Local search: sample a uniform polynomial and root find it,
# keep the point and move on
# EPZ
def local_search_sampling(Prob,D,sample_params): 
    N = Prob.num_vars

    # Search parameters; TODO: should put into a structure
    repeat_num = 10;
    chain_length = 2;
    init_perturb_num = 25;
    perturb_num = 25;
    perturb_eps = 0.01 # for ball sampling around points
    margin = 1e-6 # for flipping inequalities
    
    ###
    # This is where the actual points are sampled
    ###
    Points = [D] \
        + [perturb_dict(D,perturb_eps) for i in xrange(init_perturb_num)]   

    for i in xrange(repeat_num):
        x = VarOrder.dict2vect(D)
        for k in xrange(chain_length):
            A = None
            
            A = choose_atom_true(Prob,x)
            if A == None:
                A = choose_atom_random(Prob,x)

            # Sets up a function so that root solving it flips
            # the choosen polynomial
            f = get_num_flipping_func(A,x,margin)
            x = sp_opt.fsolve(f,x,xtol=1e-3)

            # Add this point plus some perturbed neighbours
            points =  [x]\
                + [perturb(x, perturb_eps) for i in xrange(perturb_num)]
            points = map(VarOrder.vect2dict,points)

            # Filter out points that make the main goal True (useless)
            good_on_goal = lambda y: not Prob.get_goal().eval_on_dict(y)
            points = filter(good_on_goal, points)
            Points.extend(points)

        # Filter points so we only use ones ones with a unique signature
        filtered_points = []
        SigSet = set()
        for D in Points:
            #sig = truth_sig(D)
            #if sig in SigSet:
            #    continue
            #SigSet.update(sig)
            filtered_points.append(D)
        print "Size of signature set: ", len(SigSet)
        return filtered_points
