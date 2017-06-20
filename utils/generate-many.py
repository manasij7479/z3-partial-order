import sys
import subprocess
import random

num_tests = int(sys.argv[1])
num_vars_upper_bound = int(sys.argv[2])
pos_upper_bound = int(sys.argv[3])
neg_upper_bound = int(sys.argv[4])

out_dir = "outs"

test_dir = "tests"


subprocess.Popen("mkdir " + out_dir, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
subprocess.Popen("mkdir " + test_dir, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


for i in range(0, num_tests):
  current_vars = random.randint(num_vars_upper_bound/2, num_vars_upper_bound)
  current_pos = random.randint(pos_upper_bound/4, pos_upper_bound)
  current_neg = random.randint(neg_upper_bound/4, neg_upper_bound)
  current_file = str(i)
  current_test = str(i)
  arg = "./gen-random-po " + str(current_vars) + " " + str(current_pos) + " " + str(current_neg) + " " + out_dir + "/" + current_file + ".txt " + test_dir + "/" + current_test + ".txt"
  print(arg)
  subprocess.Popen(arg, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
