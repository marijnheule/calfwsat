import os
import sys
import getopt
import functools
import time
import subprocess

def run(name, args):

  solver = None
  maxTries = None
  cutoff = None
  timeout = 500
  input_file = None
  check_witness = False
  card_compute = 1
  seed = 0
  output_file = None
  stochastic_selection = 0
  hard_eps = 0
  soft_eps = 0
  neighbors_plus = False
  ignore_weight = False
  soft_transfer = False
  soft_takes_hard = False
  wt_exp = None
  init_card_wt = None
  all_transfer = None
  transfer_slow = None
  hard_takes_soft = None
  rand_uvar = None
  sel_exp = None
  card_wt_rule = None 
  inner_bound = None 
  hit_bound = None 
  inner_mult = None 
  flip_step = None 
  hard_stochastic_selection =  None
  outer_bound = None 
  init_cls_wt = None
  cls_no_maxs_multiply = None
  init_cls_relative = None
  select_random_sat = None


  opts, args = getopt.getopt(args, "yYpFPTInws:m:c:t:i:o:r:f:S:H:E:e:C:a:R:l:q:b:z:h:Q:B:Z:g:U:")

  for (opt,value) in opts:
    if (opt == '-s'):
      solver = value
    elif (opt == '-m'):
      maxTries = int(value)
    elif (opt == '-c'):
      cutoff = int(value)
    elif (opt == '-t'):
      timeout = int(value)
    elif (opt == '-i'):
      input_file = value
    elif (opt == '-w'):
      check_witness = True
    elif (opt == '-o'):
      card_compute = int(value)
    elif (opt == '-r'):
      seed = int(value)
    elif (opt == '-f'):
      output_file = "logs/"+value
    elif (opt == '-S'):
      stochastic_selection = int(value)
    elif (opt == '-H'):
      hard_eps = int(value)
    elif (opt == '-E'):
      soft_eps = int(value)
    elif (opt == '-n'):
      neighbors_plus = True
    elif (opt == '-I'):
      ignore_weight = True
    elif (opt == '-T'):
      soft_transfer = True
    elif (opt == '-P'):
      soft_takes_hard = True
    elif (opt == '-e'):
      wt_exp = int(value)
    elif (opt == '-C'):
      init_card_wt = int(value)
    elif (opt == '-a'):
      all_transfer = int(value)
    elif (opt == '-F'):
      transfer_slow = True
    elif (opt == '-p'):
      hard_takes_soft = True
    elif (opt == '-R'):
      rand_uvar = int(value)
    elif (opt == '-l'):
      sel_exp = int(value)
    elif (opt == '-q'):
      card_wt_rule = int(value)
    elif (opt == '-b'):
      inner_bound = int(value)
    elif (opt == '-z'):
      hit_bound = int(value)
    elif (opt == '-h'):
      inner_mult = int(value)
    elif (opt == '-Q'):
      flip_step = int(value)
    elif (opt == '-B'):
      outer_bound = int(value)
    elif (opt == '-Z'):
      hard_stochastic_selection = int(value)
    elif (opt == '-g'):
      init_cls_wt = int(value)
    elif (opt == '-Y'):
      init_cls_relative = True
    elif (opt == '-y'):
      cls_no_maxs_multiply = True
    elif (opt == '-U'):
      select_random_sat = int(value)

  command = ""
  if (solver == "card_ddfw"):
    command = "time timeout {}s ./../solvers/card_ddfw ".format(timeout)
    command += " -v --cutoff={} --maxtries={} --no-witness ".format(cutoff, maxTries)
    command += " --card_compute={} ".format(card_compute)
    if stochastic_selection > 0:
      command += " --maxs_stochastic_selection={} ".format(stochastic_selection)
    if hard_eps > 0:
      command += " --maxs_hard_eps={} ".format(hard_eps)
    if soft_eps > 0:
      command += " --maxs_soft_eps={} ".format(soft_eps)
    if neighbors_plus:
      command += " --neighbors_plus=1 "
    if ignore_weight:
      command += " --ignorewtcriteria=1 "
    if soft_transfer:
      command += " --maxs_transfer_soft=1 "
    if soft_takes_hard:
      command += " --maxs_soft_takes_hard=1 "
    if wt_exp is not None:
        command += " --card_exp={} ".format(wt_exp)
    if init_card_wt is not None:
      command += " --init_card_weight={} ".format(init_card_wt)
    if all_transfer is not None:
      command += " --wt_transfer_all={} ".format(all_transfer)  
    if transfer_slow is not None:
        command += " --maxs_transfer_slow=1 "
    if hard_takes_soft is not None:
        command += " --maxs_hard_takes_soft=0 "
    if rand_uvar is not None:
        command += " --random_select={} ".format(rand_uvar)
    if sel_exp is not None:
        command += " --select_exp={} ".format(sel_exp)
    if card_wt_rule is not None:
        command += " --card_wtrule={} ".format(card_wt_rule)
    if inner_bound is not None:
        command += " --maxs_inner_bound={} ".format(inner_bound)
    if hit_bound is not None:
        command += " --maxs_hit_bound={} ".format(hit_bound)
    if inner_mult is not None:
        command += " --maxs_inner_mult={} ".format(inner_mult)
    if flip_step is not None:
        command += " --maxs_flip_step={} ".format(flip_step)
    if outer_bound is not None:
        command += " --maxs_outer_restart={} ".format(outer_bound)
    if hard_stochastic_selection is not None:
        command += " --hard_stochastic_selection={} ".format(hard_stochastic_selection)
    if init_cls_wt is not None:
        command += " --init_clause_weight={} ".format(init_cls_wt)
    if init_cls_relative is not None:
        command += " --maxs_init_weight_relative=1 "
    if cls_no_maxs_multiply is not None:
        command += " --ddfw_maxs_no_max_weight_multiply=1 "
    if select_random_sat is not None:
        command += " --clsselectp={} ".format(select_random_sat)
    command += " {} ".format(input_file)
    command += " {}".format(seed)
  elif (solver == "ddfw"):
    command = "time timeout {}s ./../solvers/ddfw ".format(timeout)
    command += " -v --cutoff={} --maxtries={} --no-witness ".format(cutoff, maxTries)
    command += " {} ".format(input_file)
    command += " {}".format(seed)
  elif (solver == "yalsat"):
    flips = cutoff * maxTries
    command = "time timeout {}s ./../solvers/yalsat ".format(timeout)
    command += " -v --no-witness --restart={} ".format(cutoff, maxTries)
    command += " {} ".format(input_file)
    command += " {} {} ".format(seed, flips)
  elif (solver == "cadical"):
    command = "time timeout {}s ./../solvers/cadical ".format(timeout)
    command += " -v "
    command += " {} ".format(input_file)
  elif (solver == "card_cadical"):
    command = "time timeout {}s ./../solvers/card_cadical ".format(timeout)
    command += " -v "
    command += " {} ".format(input_file)
  elif (solver == "carlsat"):
    command = "time ./../solvers/CarlSAT -a 2 -b 2 -c 100000 -e 100 -f 100 -x 100 "
    command += " -z {} -t {} ".format(input_file, timeout)
    command += " -s {} ".format(seed)
    command += " -v 2"
  elif (solver == "purems_mse"): # './purems <ins> <seed> <cutoff_time> <verbosity>'
    command = "time ./../solvers/purems_mse "
    command += " {} {} {} 1".format(input_file, seed, timeout)
  elif (solver == "ls-ecnf"): # './LS-ECNF <input-ecnf-file> <cutofftime> >> <output_file>'
    command = "time ./../solvers/LS-ECNF"
    command += " {} {}".format(input_file, timeout)
    # no random seed, maybe it sets the seed based on clock time? 
  

  print("\nNEXT CONFIGURATION",flush=True)
  print(command,flush=True)
  print("START CONFIGURATION\n",flush=True)
  os.system(command)
  print("\nEND CONFIGURATION\n",flush=True)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
