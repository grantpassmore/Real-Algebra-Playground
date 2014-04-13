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
  
def get_matrix(polies_size):
  global matrix_of_signs_lookup
  
  if polies_size in matrix_of_signs_lookup:
    return matrix_of_signs_lookup[polies_size]
  
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
  if polies_size > 5:
    raise Exception("more than 5 polies")
  global matrix_of_signs_inverse_lookup
  
  if polies_size in matrix_of_signs_inverse_lookup:
    return matrix_of_signs_inverse_lookup[polies_size]
  
  
  matrix = get_matrix(polies_size)
  
  print "calculating matrix_of_signs_inverse for %d" %polies_size
  inverse = matrix.inv()
  
  matrix_of_signs_inverse_lookup[polies_size] = inverse
  
  write_to_cache('matrix_of_signs_inverse.pkl', matrix_of_signs_inverse_lookup)
  
  return inverse  