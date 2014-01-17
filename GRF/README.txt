--{New setup notes, only depending on Sage}--

1) Run the Sage command line shell.
   On Ohmu, the Sage binary should be in the path, so you can just run `sage':

     > sage

2) Within Sage, execute the commands:

     > load('grf.sage')
     > load('smt2.py')
     > grf_on_file('my_input_file.smt', outfile='foo.out', k=25, epsilon=0.1, interactive=False)

       * Note that all keyword parameters to grf_on_file are optional.

       * Note that the result of GRF on a problem may vary significantly as
         the k and epsilon parameters are varied.

   * For a concrete example on Ohmu:

     > grf_on_file('/usr0/home/grantp/GRF/Examples/HidingProblems/DWA_StationaryObstacles_ArcTraj_onlyleaves_nodivision_lessstupid.key_10.smt', interactive=True)

3) For experimenting with sampling techniques, search in grf.sage for the phrase `Note for Erik'.

4) Please let me know if you have any trouble!

-G. Passmore - 15/Dec/2013





          **********





--{Old setup notes, for use with Gurobi}--

Setup notes for GRF:

1) Install Gurobi 5.5 (you can get a free academic license).

2) Install Sage (any relatively recent version should work).

3) Unzip the archive grf.tgz. Let's call the directory in which you unpacked the archive $GRF.

4) If you're using Sage based on Python 3.x, then modify the pyparsing import in $GRF/smt2.py.
   (*Probably, you won't need to do this modification.)

   If you do get errors regarding pyparsing, then perform the modification of $GRF/smt2.py
   as directed by this comment in $GRF/smt2.py:

    #  * Note: If you're using Sage with Python 3.x,
    #          change pyparsing_py2 to pyparsing_py3 in the import below.

5) Modify the value of bin_path in $GRF/grf.sage to point to $GRF.

6) Verify that running $GRF/muse.py --help prints a help screen without giving
   any errors.

   If instead of seeing the help screen, you see an error like:

                Traceback (most recent call last):
                  File "./muse.py", line 19, in <module>
                    from gurobipy import *
                ImportError: No module named gurobipy

   then:

    6a) Start a fresh shell and run python.
    6b) Verify that importing gurobipy causes no errors, e.g.,

         >>> import gurobipy

        should give no output. If you see something like:

                Traceback (most recent call last):
                  File "<stdin>", line 1, in <module>
                ImportError: No module named gurobipy

        then your Gurobi environment was not successfully setup.
        Assuming all is well:

    6c) Execute the following commands:

         >>> import sys
         >>> sys.path

        Copy the output of sys.path (a list) as the value of sys.path
        in muse.py.


    6d) Verify that running $GRF/muse.py --help prints the help screen.

7) Run the sage command line shell.

8) Execute the commands:

    > load('grf.sage')
    > load('smt2.py')
    > grf_on_file('my_input_file.smt', outfile='foo.out', k=25, epsilon=0.1, interactive=False)

  * Note that all keyword parameters to grf_on_file are optional.

  * Note that the result of GRF on a problem may vary significantly as
    the k and epsilon parameters are varied.

9) Hopefully that should work without issue!
