"""Wrapper module for sympy library that caches results

Exposes polynomial algebra operations
"""

import time

#TODO remove
import sympy

import sympywrapper as w
from muchnik import AlgebraAPIWrapper


class CachedSympyWrapper(AlgebraAPIWrapper):
  """Implements methods of AlegbraAPIWrapper from muchnik
  """

  def timer(self, count, f, *args):
    if len(args) > 1:
      foo = lambda x : f(args[0], x)
      return self.timer(count, foo, *args[1:])
    print "starting"
    start = time.time()
    for i in range(count):
        f(args[0])
    end = time.time()
    print (end - start)
    print "avg: %s" %((end - start)/count)
    print "ending"
    return f(args[0])

  def _c_get(self, cache, *args):
    if cache.has_key(args[0]) == False:
      return None
    if len(args) == 1:
      return cache[args[0]]
    return self._c_get(cache[args[0]], *args[1:])

  def _c_put(self, cache, value, *args):
    if(len(args) == 1):
      cache[args[0]] = value
      return 
    if cache.has_key(args[0]) == False:
      new_cache = {}
      cache[args[0]] = new_cache
      self._c_put(new_cache, value, *args[1:])
    next_cache = cache[args[0]]
    self._c_put(next_cache, value, *args[1:])
  
  def __init__(self, eliminate_variable):
    """Constructs a algebra, where operations are done with respect 
    to a single variable
    
    Keyword arguments:
    eliminate_variable -- variable which is to be eliminated from muchnik
    """
    self._variable = eliminate_variable
    self._underlying = w.SympyWrapper(eliminate_variable)
    self._cache = {}
  
  def _c_compute(self, f, *args):
    cache_result = self._c_get(self._cache, f, args)
    if cache_result != None:
      return cache_result
    if len(args) == 1:
      ret = f(args[0])
    elif len(args) == 2:
      ret = f(args[0], args[1])
    else:
      raise Exception("not impl yet")
    self._c_put(self._cache, ret, f, args)
    return ret


  def LT(self, p):
    return self._c_compute(self._underlying.LT, p)

  def LC(self, p):
    return self._c_compute(self._underlying.LC, p)
    
  def LS(self, p):
    return self._c_compute(self._underlying.LS, p)
    
  def degree(self, p):
    return self._c_compute(self._underlying.degree, p)
    
  def div(self, p, q):
    return self._c_compute(self._underlying.div, p, q)
    
  def p_tail(self, p):
    return self._c_compute(self._underlying.p_tail, p)
    
  def e_var(self):
    return self._underlying.e_var()
    
  def has_variable(self, p):
    return self._c_compute(self._underlying.has_variable, p)

  def pseudo_div(self, p, q):
    return self._c_compute(self._underlying.pseudo_div, p, q)
    
  def derivative(self, p):
    return self._c_compute(self._underlying.derivative, p)

  def zero(self):
    return self._underlying.zero()

  def sign(self, scalar):
    return self._underlying.sign(scalar)

