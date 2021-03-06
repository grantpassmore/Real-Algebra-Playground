--{New setup notes, only depending on Sage}--

1) Run the Sage command line shell.

     > sage

2) Within Sage, execute the commands:

     > load('grf.sage')
     > load('smt2.py')
     > grf_on_file('my_input_file.smt', outfile='foo.out', k=25, epsilon=0.1, interactive=False)

       * Note that all keyword parameters to grf_on_file are optional.

       * Note that the result of GRF on a problem may vary significantly as
         the k and epsilon parameters are varied.

   * For a concrete example:

     > grf_on_file('./Examples/HidingProblems/DWA_StationaryObstacles_ArcTraj_onlyleaves_nodivision_lessstupid.key_10.smt', interactive=True)

3) For experimenting with sampling techniques, search in grf.sage for the phrase `Note for Erik'.

4) Please let me know if you have any trouble!

-G. Passmore - 15/Dec/2013
