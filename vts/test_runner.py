import unittest

import test_vts
import test_grf_parser
import test_isym

if __name__ == "__main__":
  suite1 = unittest.TestLoader().loadTestsFromTestCase( \
      test_vts.VTSTest)
  suite2 = unittest.TestLoader().loadTestsFromTestCase( \
      test_grf_parser.TestGRFParser)
  suite3 = unittest.TestLoader().loadTestsFromTestCase( \
      test_isym.TestIsym)

  suite = unittest.TestSuite([suite1, suite2, suite3])
  unittest.TextTestRunner(verbosity = 2).run(suite)
