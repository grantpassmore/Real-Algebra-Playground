import cohenhorm
import sympywrapper
import sympy

import unittest
import fractions

def f(d, n):
  return fractions.Fraction(d, n)
  

class CohenHormanderTest(unittest.TestCase):
  
  def setUp(self):
    self.x = sympy.var('x')
    self.ch = cohenhorm.CohenHormander(sympywrapper.SympyWrapper(x))
  
  
  def _fill_diagram_with_value(self, diagram, p, value, colCount):
    diagram[p] = {}
    for d in range(colCount):
      diagram[p][ f(d, colCount - 1) ] = value
      
  def check_tables(self, expected, actual):
    #self.ch.pprint_diagram(expected)
    #self.ch.pprint_diagram(actual)
  
    self.assertEquals(expected.keys(), actual.keys())
    for row in expected.keys():
      self.assertEquals(len(expected[row].keys()), 
          len(actual[row].keys()))
      for (exp_col, act_col) in zip(sorted(expected[row]), sorted(actual[row])):
        self.assertEquals(expected[row][exp_col], 
            actual[row][act_col])
  
  def test_copy_table_keep_all(self):
    p1 = self.x
    p2 = self.x * 2
    
    all_table = {}
    self._fill_diagram_with_value(all_table, p1, 1, 7)
    all_table[p1][f(2,6)] = 0
    self._fill_diagram_with_value(all_table, p2, -1, 7)
    all_table[p2][f(4,6)] = 0
    
    table = self.ch.copy_table(all_table,[p1, p2],{})
    
    expected_table = {}
    self._fill_diagram_with_value(expected_table, p1, 1, 7)
    expected_table[p1][f(2,6)] = 0
    self._fill_diagram_with_value(expected_table, p2, -1, 7)
    expected_table[p2][f(4,6)] = 0
    
    self.check_tables(expected_table, table)
  
  def test_copy_table_keep_one(self):
    p1 = self.x
    p2 = self.x * 2
    
    all_table = {}
    self._fill_diagram_with_value(all_table, p1, 1, 7)
    all_table[p1][f(2,6)] = 0
    self._fill_diagram_with_value(all_table, p2, -1, 7)
    all_table[p2][f(4,6)] = 0
    
    table = self.ch.copy_table(all_table,[p1],{})
    
    expected_table = {}
    self._fill_diagram_with_value(expected_table, p1, 1, 5)
    expected_table[p1][f(1, 2)] = 0
    
    self.check_tables(expected_table, table)  
    
if __name__ == "__main__":
  suite = unittest.TestLoader().loadTestsFromTestCase( \
              CohenHormanderTest)
  
  unittest.TextTestRunner(verbosity=2).run(suite)