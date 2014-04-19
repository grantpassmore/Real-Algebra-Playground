import pickle
import os
import errno

import sympy
import sympy.physics.quantum

# TODO create separate cache module
def write_to_cache(name, obj):
  try:
    os.makedirs('cache')
  except OSError as exception:
    if exception.errno != errno.EEXIST:
      raise exception
  with open(os.path.join('cache', name), 'wb') as f:
    pickle.dump(obj, f)
def cache_hit(name):
  return os.path.isfile(os.path.join('cache', name))
def read_cache(name):
  with open(os.path.join('cache', name), 'rb') as f:
    return pickle.load(f)
    
def load_or_create_matrix():
  # TODO remove old implementation
  """
  print "matrix_of_signs.load_or_create_matrix is temporary broken"
  print "comment 'return None' out"
  print "this is not a bug (want to switch to faster implementation after"
  print "unittest, but don't wan't to wait on init in the meantime)"
  print
  print
  """
  return None
  print 'loading'

  cache_key = 'matrix_of_signs.pkl'
  if cache_hit(cache_key):
    print 'getting from cache'
    return read_cache(cache_key)
    
  print 'creating new'
  ret = {1: sympy.Matrix(sympy.Matrix([[1, 1, 1], [0, 1, -1], [0, 1, 1]]))}
  write_to_cache(cache_key, ret)
  return ret

  
matrix_of_signs_lookup = load_or_create_matrix()

new_matrix_of_signs_lookup = {1: sympy.Matrix(sympy.Matrix([[1, 1, 1], [0, 1, -1], [0, 1, 1]]))}
new_matrix_of_signs_inverse_lookup = {1: new_matrix_of_signs_lookup[1].inv()}


# TODO make matrix immutable
def new_get_matrix(n):
  """Return the matrix of signs that corresponds to a number of polynomials

  Keyword arguments:
  n -- number of polynomials
  
  return -- matrix of signs
  """
  global new_matrix_of_signs_lookup

  lookup = new_matrix_of_signs_lookup

  if not isinstance(n, int):
    raise Exception("%s is not an int" %n)
  if n < 1:
    raise Exception("%d is < 1" %n)  

  if n in lookup:
    return lookup[n]

  if n > 5:
    raise Exception("more than 5 polies")
  
  name = "matrix_of_signs_%d.pkl" %n

  if cache_hit(name):
    print "hit for %d" %n
    matrix = read_cache(name)
    lookup[n] = matrix
    return matrix

  
  print "miss for %d" %n
  previous = new_get_matrix(n-1)
  first = new_get_matrix(1)
  current = sympy.physics.quantum.TensorProduct(previous, first)
  write_to_cache(name, current)
  lookup[n] = current

  return current

def new_get_matrix_inverse(n):
  """Return the inverse of the matrix of signs that corresponds to a number of 
  polynomials.

  Keyword arguments:
  n -- number of polynomials
  
  return -- inverse of matrix of signs
  """
  global new_matrix_of_signs_inverse_lookup

  lookup = new_matrix_of_signs_inverse_lookup

  if not isinstance(n, int):
    raise Exception("%s is not an int" %n)
  if n < 1:
    raise Exception("%d is < 1" %n)

  if n in lookup:
    return lookup[n]

  if n > 5:
    raise Exception("more than 5 polies")
  
  name = "matrix_of_signs_inverse_%d.pkl" %n

  if cache_hit(name):
    print "inv hit for %d" %n
    matrix = read_cache(name)
    lookup[n] = matrix
    return matrix

  
  print "inv miss for %d" %n

  matrix = new_get_matrix(n)
  
  print "calculating matrix_of_signs_inverse for %d" %n
  inverse = matrix.inv()

  write_to_cache(name, inverse)
  lookup[n] = inverse

  return inverse

def get_matrix(polies_size):
  return new_get_matrix(polies_size)
  global matrix_of_signs_lookup
  
  if polies_size in matrix_of_signs_lookup:
    return matrix_of_signs_lookup[polies_size]

  if polies_size > 5:
    raise Exception("more than 5 polies")

  previous = get_matrix(polies_size - 1)
  first = get_matrix(1)
  
  
  print "calculating matrix_of_signs for %d" %polies_size
  current = sympy.physics.quantum.TensorProduct(previous, first)
  matrix_of_signs_lookup[polies_size] = current
  
  write_to_cache('matrix_of_signs.pkl', matrix_of_signs_lookup)
  
  return current

def load_or_create_inverse():
  print 'loading'
  cache_key = 'matrix_of_signs_inverse.pkl'
  if cache_hit(cache_key):
    print 'getting from cache'
    return read_cache(cache_key)
    
  print 'creating new'
  
  ret = {1: get_matrix(1).inv()}
  write_to_cache(cache_key, ret)
  return ret  
  
matrix_of_signs_inverse_lookup = load_or_create_inverse()

def get_matrix_inverse(polies_size):
  return new_get_matrix_inverse(polies_size)
  global matrix_of_signs_inverse_lookup
  
  if polies_size in matrix_of_signs_inverse_lookup:
    return matrix_of_signs_inverse_lookup[polies_size]

  if polies_size > 5:
    raise Exception("more than 5 polies")
  
  matrix = get_matrix(polies_size)
  
  print "calculating matrix_of_signs_inverse for %d" %polies_size
  inverse = matrix.inv()
  
  matrix_of_signs_inverse_lookup[polies_size] = inverse
  
  write_to_cache('matrix_of_signs_inverse.pkl', matrix_of_signs_inverse_lookup)
  return inverse  
