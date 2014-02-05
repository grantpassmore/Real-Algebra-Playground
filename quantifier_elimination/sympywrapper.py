"""Wrapper module for sympy library

Exposes polynomial algebra operations
"""

import sympy

from muchnik import AlgebraAPIWrapper


class SympyWrapper(AlgebraAPIWrapper):
  """Implements methods of AlegbraAPIWrapper from muchnik
  """
  
  def __init__(self, eliminate_variable):
    """Constructs a algebra, where operations are done with respect 
    to a single variable
    
    Keyword arguments:
    eliminate_variable -- variable which is to be eliminated from muchnik
    """
    self._variable = eliminate_variable
  
  def LT(self, p):
    return sympy.LT(p, self._variable)

  def LC(self, p):
    return sympy.LC(p, self._variable)
    
  def LS(self, p):
    symbols = p.free_symbols
    symbols.add(self._variable)
    return sympy.LC(p, symbols)
    
  def degree(self, p):
    return sympy.degree(p, self._variable)
    
  def div(self, p, q):
    return sympy.div(p, q, self._variable)
    
  def p_tail(self, p):
    return (p - self.LT(p)).expand()
    
  def e_var(self):
    return self._variable
    
  def has_variable(self, p):
    return len(p.free_symbols) > 0

  def pseudo_div(self, p, q):
    return sympy.pdiv(p, q, self._variable)
    
  def derivative(self, p):
    return sympy.diff(p, self._variable)

  def zero(self):
    return sympy.Integer(0)

  def sign(self, scalar):
    return sympy.sign(scalar)

