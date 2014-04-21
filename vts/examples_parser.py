"""Module for parsing GRF format examples.
Supports faster parsing from pickled python objects.
"""

import sys
import os
import errno
import pickle
import itertools

import sympy

import grf_parser as gparser
import isym

x = sympy.var('x')

# "With pyparsing, the default sys recursion limit must be increased for
#   parsing w.r.t. even relatively small recursive grammars."
# -- https://github.com/grantpassmore/Real-Algebra-Playground/blob/master/GRF/smt2.py
sys.setrecursionlimit(2 ** 20)


def write_sympy_parseable_examples():
  """Parses examples form ../GRF/Examples directory and pickles them to 
  ./Examples directory
  """
  
  dir_examples = examples_preformat_uni()
  
  for dir in dir_examples:
    try:
      os.makedirs(os.path.join('Examples', dir))
    except OSError as exception:
      if exception.errno != errno.EEXIST:
          raise exception
    for file in dir_examples[dir]:
      print file
      # could do it manually (which might make it faster)
      with open(os.path.join('Examples', dir, file + '.pkl'), 'wb') as f:
        pickle.dump(dir_examples[dir][file], f)
      
  
def examples_preformat_uni():
  """Converts examples to be univariate
  
  Keyword arguments:
  return -- map of maps where first level key is directory name,
  second level keys are file names and values are lists of examples in that file.
  Single example consists of tuples (antecent, succedent)
  
  """
  dirResults = parse_example_dirs()
  dirFormulas  = {}
  for dir in dirResults:
    fileFormulas = {}
    for file in dirResults[dir]:
      file_examples = []
      for example in dirResults[dir][file]: 
        #print example
        #print example['antecedent']['fmls']
        
        uni_ante = make_univariate(example['antecedent']['fmls'])
        uni_succ = make_univariate(example['succedent']['fmls'])
        file_examples.append((uni_ante, uni_succ))
        #formulas = vts_preformat(uni_ante, uni_succ)
      fileFormulas[file] = file_examples
    dirFormulas[dir] = fileFormulas
  return dirFormulas
      

def make_univariate(relations):
  """Converts a list of relations to univariate ones
  and transforms right hand sides of relations to zero.
  
  Keyword arguments:
  relations -- list of sympy relations (multivariate, arbitrary relations)
  
  return -- lists of univariate relations that have right hand side of zero
  """
  acc = []
  for relation in relations:
    old_relation = relation.lhs - relation.rhs
    vars = old_relation.free_symbols
    zipped_vars = zip(vars, map(lambda p: x, range(len(vars))))
    new_lhs = old_relation.subs(zipped_vars).expand()
    cls = relation.__class__
    acc.append(cls(new_lhs, 0))
  return acc

def unpickle_dirs_gen():
  base_dir = os.path.join('Examples')
  met_dir = os.path.join(base_dir, 'MetiTarski')
  hid_dir = os.path.join(base_dir, 'HidingProblems')

  dirGen = itertools.chain( os.walk(met_dir), os.walk(hid_dir))

  all_names = []
  for dirpath, dirnames, filenames in dirGen:
    all_names += map(lambda s: os.path.join(dirpath, s), filenames)

  def unpickle_file(filename):
    with open(filename, 'rb') as f:
      shorter = os.path.basename(filename)
#      print 
      sys.stdout.write("parsing %s" %shorter)
      sys.stdout.flush()


      content = pickle.load(f)

      sys.stdout.write("\rdone parsing %s\n" %shorter)
      sys.stdout.flush()
      return content

  return itertools.imap(unpickle_file, all_names)

def unpickle_dirs():
  """Loads python objects from "./Examples" directory
  
  
  Keyword arguemtns:
  
  return -- map of maps where first level key is directory name,
  second level keys are file names and values are lists of examples in that file.
  Single example consists of tuples (antecent, succedent)
  
  """
  base_dir = os.path.join('Examples')
  met_dir = os.path.join(base_dir, 'MetiTarski')
  hid_dir = os.path.join(base_dir, 'HidingProblems')
  
  met_results = unpickle_from_dir(met_dir)
  hid_results = unpickle_from_dir(hid_dir)
  return {
    'Metitarski':met_results, 
    'HidingProblems':hid_results
  }
  
def unpickle_from_dir(dir):
  """Unpickles files in directory
  
  Keyword arguments:
  dir -- directory where files are located
  
  return -- map with file names as keys and unpickled objects as values
  """
  print "unpickling examples from %s" %dir
  ret = {}
  for dirpath, dirnames, filenames in \
      os.walk(dir):
    for filename in filenames:
      print filename
      with open(os.path.join(dirpath, filename), 'rb') as f:
        content = pickle.load(f)
        ret[filename] = content
      # break
  return ret  
  
def parse_example_dirs():
  """Parses examples in ../GRF/Examples/Metitarski and 
  ../GRF/Examples/HidingProblems.
  
  Keyword arguments:
  return -- two level where first level keys are directories, second level keys
  are file names and values are examples in those files.
  
  """
  base_dir = os.path.join('..', 'GRF', 'Examples')
  met_dir = os.path.join(base_dir, 'MetiTarski')
  hid_dir = os.path.join(base_dir, 'HidingProblems')
  
  met_results = parse_files_from_dir(met_dir)
  #hid_results = parse_files_from_dir(hid_dir)
  return {
    'Metitarski':met_results, 
    #'HidingProblems':hid_results
  }
  
def parse_files_from_dir(dir):
  """Parses files from directory
  
  Keyword arguments:
  dir -- directory where files are located
  
  return -- map with filenames as keys and examples in those files as values.
  """
  print "parsing examples from %s" %dir
  ret = {}
  count = 0
  for dirpath, dirnames, filenames in \
      os.walk(dir):
    for filename in filenames:
      count += 1
      #if not count in range(50, 90):
      #  continue
      print filename
      f = open(os.path.join(dirpath, filename))
      
      content = f.read()
      #print "len: %d" %len(list(gparser.lit_sequent.scanString(content)))
      #print "len: %d" %len(list(gparser.cmd.scanString(content)))
      
      resultList = []
      for results, start, end in gparser.cmd.scanString(content):
        #print results
        resultList.append(results)
      ret[filename] = resultList
      
      #break #TODO delete when parsing all files
  return ret  
