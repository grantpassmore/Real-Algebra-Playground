import glob
import time
import sys, os
from collections import namedtuple
import random
import multiprocessing as mp
import numpy as np
import math

# Config
Timeout = 1800 # 30 minutes
Cores = 30
SMT_Files = glob.glob("/usr0/home/grantp/GRF/Examples/HidingProblems/*.smt")
#Files_Indices = [26,29,28,24,25,23,22,21,20,18,17,14,10,9,3,0,1]
Files_Indices = [22]
#Files_Indices = range(len(SMT_Files))

param_samples = 180
sample_dist = lambda: random.randint(0,500)
epsilon_dist = lambda: 0.05*random.random()

ParamStruct = namedtuple("ParamStruct", "smt_file file_id epsilon samples")
ProcessStruct = namedtuple("ProcessStruct", "id, start_time, process, params")

suppress_output = True


# Run a specific test for different epsilions
def trial(params, proc_id, return_dict):
  r = grf_on_file(params.smt_file,\
                    interactive=False,\
                    epsilon=params.epsilon,\
                    k=params.samples)
  return_dict[proc_id] = r


"""
Main function
"""
if __name__ == '__main__':
  FH = open("test.csv","w") 
  FH.write("# Samples, Epsilon, Time, Hides\n");
  load('grf.sage')
  load('smt2.py')

  # Queue up the trial parameters
  param_queue = [];
  F = len(SMT_Files)
  for file_id in Files_Indices:
    smt_file = SMT_Files[file_id]
    for j in xrange(param_samples):
      epsilon = epsilon_dist()
      samples = sample_dist()
      
      params = ParamStruct(smt_file,file_id,epsilon,samples)
      param_queue.append(params)
  TotalPQ = len(param_queue)
  # Init the running queue
  master_id = 1;
  running_queue=[]
  if suppress_output:
    sys.stdout = open(os.devnull,'w') # Turn off noise


  # Set up a shared datastructure for returned data
  manager = mp.Manager()
  return_dict = manager.dict()

  # Run the queues
  Times = []
  PQ = len(param_queue)
  RQ = len(running_queue)
  while (PQ > 0 or RQ > 0):
    # Check for finished jobs and timeouts
    assert(PQ == len(param_queue))
    assert(RQ == len(running_queue))
    for i in range(RQ):
      proc_struct = running_queue[i]
      elapsed = time.time() - proc_struct.start_time
      # Check for finished
      if not proc_struct.process.is_alive():
        # Running time
        Times.append(elapsed)
        sys.stderr.write('Removed {0}; finished ({1}s)\n'\
                           .format(proc_struct.id, elapsed))
        hides = sum(return_dict[proc_struct.id])
        FH.write(",".join(map(str, [proc_struct.params.file_id,\
                                      proc_struct.params.samples,\
                                      proc_struct.params.epsilon,\
                                      elapsed,\
                                      hides])) + "\n")
        running_queue.pop(i)
        RQ = RQ - 1;
        break

      # Check for timed out
      if elapsed > Timeout:
        Times.append(float('inf'))
        sys.stderr.write('Removed {0}; timeout\n'.format(proc_struct.id))
        FH.write(",".join(map(str, [proc_struct.params.file_id,\
                                      proc_struct.params.samples,\
                                      proc_struct.params.epsilon,\
                                      "NaN",\
                                      "NaN"])) + "\n")
        proc_struct.process.terminate();
        running_queue.pop(i)
        RQ = RQ - 1;
        break

    # Restock queue
    assert(PQ == len(param_queue))
    assert(RQ == len(running_queue))
    while PQ > 0 and RQ < Cores:
      params = param_queue.pop()
      proc_struct = ProcessStruct(master_id,\
                                    time.time(),\
                                    mp.Process(target=trial,\
                                                 args=[params,\
                                                         master_id,\
                                                         return_dict]),\
                                    params)
      proc_struct.process.start()
 
      PQ = PQ - 1
      RQ = RQ + 1
      master_id = master_id + 1
      running_queue.append(proc_struct)
      sys.stderr.write('Starting {0} ({1} remaining; {2}% done)\n'\
                         .format(proc_struct.id,\
                                   PQ,\
                                   100.0 - 100.0*float(PQ)/float(TotalPQ)))
           
    time.sleep(0.01)
  if suppress_output:
    sys.stdout = sys.__stdout__
  sys.stderr.write('10P = {0}\nMedian = {1}\n90P = {2}\n'\
                     .format(np.percentile(Times,int(10)),\
                               np.percentile(Times,int(50)),\
                               np.percentile(Times,int(90))))

  for k in return_dict.keys():
    print "job[{0}]: {1}".format(k, return_dict[k])
  FH.close()
