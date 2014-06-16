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
    
matrix_of_signs_lookup = {
    1: sympy.Matrix(sympy.Matrix([[1, 1, 1], [0, 1, -1], [0, 1, 1]]))
}
matrix_of_signs_inverse_lookup = {1: matrix_of_signs_lookup[1].inv()}


# TODO make matrix immutable
def get_matrix(n):
  """Return the matrix of signs that corresponds to a number of polynomials

  Keyword arguments:
  n -- number of polynomials
  
  return -- matrix of signs
  """

  global matrix_of_signs_lookup

  lookup = matrix_of_signs_lookup

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
  previous = get_matrix(n-1)
  first = get_matrix(1)
  current = sympy.physics.quantum.TensorProduct(previous, first)
  write_to_cache(name, current)
  lookup[n] = current

  return current

def get_matrix_inverse(n):
  """Return the inverse of the matrix of signs that corresponds to a number of 
  polynomials.

  Keyword arguments:
  n -- number of polynomials
  
  return -- inverse of matrix of signs
  """
  global matrix_of_signs_inverse_lookup

  lookup = matrix_of_signs_inverse_lookup

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

  matrix = get_matrix(n)
  
  print "calculating matrix_of_signs_inverse for %d" %n
  inverse = matrix.inv()

  write_to_cache(name, inverse)
  lookup[n] = inverse

  return inverse

