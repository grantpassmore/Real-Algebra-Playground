import multiprocessing as mp
import time

p = mp.Process(target=time.sleep, args=[1000])
p.start()
print p, p.is_alive()
p.terminate()
time.sleep(0.04)
print p, p.is_alive()
