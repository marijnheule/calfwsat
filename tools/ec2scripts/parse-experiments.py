import os
import sys
import getopt
import functools
import time
import subprocess
import csv


# tikz

def add_tikz_header ():
  s = '''\\documentclass[tikz, border=0pt]{standalone}

  \\usepackage{pgfplots}
  \\usepgfplotslibrary{patchplots}
  \\pgfplotsset{compat=1.16}

  \\definecolor{redorange}{rgb}{0.878431, 0.235294, 0.192157}
  \\definecolor{lightblue}{rgb}{0.552941, 0.72549, 0.792157}
  \\definecolor{clearyellow}{rgb}{0.964706, 0.745098, 0}
  \\definecolor{clearorange}{rgb}{0.917647, 0.462745, 0}
  \\definecolor{mildgray}{rgb}{0.54902, 0.509804, 0.47451}
  \\definecolor{softblue}{rgb}{0.643137, 0.858824, 0.909804}
  \\definecolor{bluegray}{rgb}{0.141176, 0.313725, 0.603922}
  \\definecolor{lightgreen}{rgb}{0.709804, 0.741176, 0}
  \\definecolor{redpurple}{rgb}{0.835294, 0, 0.196078}
  \\definecolor{midblue}{rgb}{0, 0.592157, 0.662745}
  \\definecolor{clearpurple}{rgb}{0.67451, 0.0784314, 0.352941}
  \\definecolor{browngreen}{rgb}{0.333333, 0.313725, 0.145098}
  \\definecolor{darkestpurple}{rgb}{0.396078, 0.113725, 0.196078}
  \\definecolor{greypurple}{rgb}{0.294118, 0.219608, 0.298039}
  \\definecolor{darktruqoise}{rgb}{0, 0.239216, 0.298039}
  \\definecolor{darkbrown}{rgb}{0.305882, 0.211765, 0.160784}
  \\definecolor{midgreen}{rgb}{0.560784, 0.6, 0.243137}
  \\definecolor{darkred}{rgb}{0.576471, 0.152941, 0.172549}
  \\definecolor{darkpurple}{rgb}{0.313725, 0.027451, 0.470588}
  \\definecolor{darkestblue}{rgb}{0, 0.156863, 0.333333}
  \\definecolor{lightpurple}{rgb}{0.776471, 0.690196, 0.737255}
  \\definecolor{softgreen}{rgb}{0.733333, 0.772549, 0.572549}
  \\definecolor{offwhite}{rgb}{0.839216, 0.823529, 0.768627}


  \\begin{document}'''

  return s

def add_plot_header (title,xlabel,  xmin, xmax, ylabel, ymin, ymax, formula):

  title = ('-').join(title.split('_'))

  ylabel = "percent gap XPress 45min"
  if ymin is None: 
    if formula is not None :
      if formula == "mm-SR03.wknf" or formula == "mm-SR03.wcard":
        ymin = 98
        ymax = 102
      elif formula == "mm-SR05.wknf" or formula == "mm-SR05.wcard":
        ymax = 104
        ymin = 94
      elif formula == "mm-SW02.wknf" or formula == "mm-SW02.wcard":
        ymax = 104
        ymin = 98
      elif formula == "mm-SW05.wknf" or formula == "mm-SW05.wcard":
        ymax = 106
        ymin = 92

  
  
  s = "\\begin{tikzpicture}[scale = 1]\n\\begin{axis}[mark options={scale=1.0},grid=both, grid style={black!10},  legend style={at={(0.8,1)}}, legend cell align={left},\nx post scale=1,xlabel="+xlabel+", ylabel="+ylabel+",mark size=3pt, height=12cm,width=12cm,xtick={0,500,...,2500},xmin="+str (xmin)+",xmax="+str (xmax)+", ymin="+str (ymin)+",ymax="+str (ymax)+", title={"+title+"}]\n"

  return s

def add_dashed_line ():
  return "\\addplot[color=black,dashed] coordinates { (2700,90)(2700,110) };"

def add_plot_tail() :
  s = "\\end{axis}\n\\end{tikzpicture}\n\\end{document}"
  return s

def add_other_baselines (formula, start, end):
  # SW02 SW05 SR03 SR05
  # cplex = [98.2, 93.16, 99.1, 103.85] # [, , 98.6, 100.44]
  # gurobi = [98.14, 92.96, 98.5, 95.21]
  # carlsat = [99.35, 98.43, 99.13, 98.32]
  # calfsat = [98.99, 95.39, 98.72, 96.19] # 7/26/23


  cplex = [2298342, 559338, 5183007, 1456560] # [, , 98.6, 100.44]
  gurobi = [2299170, 562678, 5177754, 1380699]
  carlsat = [99.35, 98.43, 99.13, 98.32]


  if formula is not None :
    bidx = -1
    if formula == "mm-SR03.wknf" or formula == "mm-SR03.wcard":
      bidx = 2
    elif formula == "mm-SR05.wknf" or formula == "mm-SR05.wcard":
      bidx = 3
    elif formula == "mm-SW02.wknf" or formula == "mm-SW02.wcard":
      bidx = 0
    elif formula == "mm-SW05.wknf" or formula == "mm-SW05.wcard":
      bidx = 1
  
    # add plots for 
    s = add_line_prefix ('midgreen',None,None,None,None,1)
    s += add_point (start, get_percentage (formula, cplex[bidx]))
    s += add_point (end, get_percentage (formula, cplex[bidx]))
    s += add_end_line () + "\n"

    s += add_line_prefix ('blue',None,None,None,None,1)
    s += add_point (start, get_percentage (formula, gurobi[bidx]))
    s += add_point (end, get_percentage (formula, gurobi[bidx]))
    s += add_end_line () + "\n"

    s += add_line_prefix ('clearpurple',None,None,None,None,1)
    s += add_point (start, 100)
    s += add_point (end, 100)
    s += add_end_line () + "\n"

    s += add_line_prefix ('lightblue',None,None,None,None,1)
    s += add_point (start, carlsat[bidx])
    s += add_point (end, carlsat[bidx])
    s += add_end_line () + "\n"

    # s += add_line_prefix ('orange',None,None,None,1,1)
    # s += add_point (start, calfsat[bidx])
    # s += add_point (end, calfsat[bidx])
    # s += add_end_line () + "\n"

  return s

def add_line_prefix (color, mark, size, opacity, dashed, thick=None) :
  s = "\\addplot[color="+color
  if mark is not None: s += ",mark="+mark
  if size is not None: s += ",mark size="+str (size)+"pt"
  if opacity is not None: s+= ",opacity="+str (opacity)
  if dashed is not None: s+= ",dashed"
  if thick is not None: s+= ",ultra thick"
  
  s+= "] coordinates { "

  return s

def add_point (x,y):
  s = "("+str(x) + "," + str(y) + ")"
  return s

def add_end_line () : return " };"

def add_legend (list) :
  s = ""
  for l in list:
    s += str(l) + ", "
  return "\legend{" + s[:-2] + "}"

# generally of the form ../../benchmarks/knf/iso-10-18.knf
def get_formula (line) :
  s = ""
  for c in line:
    if c == '/': s = ""
    else: s += c
  return s

def get_argument (line, prefix) :
  l = len(prefix)
  tokens = line.split()
  res = None
  for token in tokens:
    if len(token) > l and token[:l] == prefix:
      res = int (token[l:])
      break

  return res

def get_argument_t (tokens, prefix) :
  l = len(prefix)
  res = None
  for token in tokens:
    if len(token) > l and token[:l] == prefix:
      res = int (token[l:])
      break

  return res
      

def get_configuration (line) :
  config_dic = {}
  solver = None
  formula = None
  config_name = ""
  seed = 0
  tokens = line.split()

  config_dic['config_line'] = line

  if "solvers/card_ddfw" in line:
    solver = "card_ddfw"
    if "--card_compute=1" in line:
      config_name += "card=Lin"
    elif "--card_compute=2" in line:
      config_name += "card=Exp"
    elif "--card_compute=3" in line:
      config_name += "card=Quad"
    elif "--card_compute=4" in line:
      config_name += "card=LinExp"

    hard_eps = get_argument (line, "--maxs_hard_eps=")
    soft_eps = get_argument (line, "--maxs_soft_eps=")
    if hard_eps is not None:
      config_name += "_heps="+str (hard_eps)
    if soft_eps is not None:
      config_name += "_seps="+ str(soft_eps)
    
    stoch_sel = get_argument (line, "--maxs_stochastic_selection=")
    if stoch_sel is not None:
      config_name += "_select=" + str ( stoch_sel )
      config_dic['stoch_sel'] = stoch_sel

    k_exp = get_argument (line, "--card_exp=")
    if k_exp is not None:
      config_name += "_ex=" + str ( k_exp )
      config_dic['k_exp'] = k_exp

    init_card = get_argument (line, "--init_card_weight=")
    if init_card is not None:
      config_name += "_initCard=" + str ( init_card )
      config_dic['init_card'] = init_card

    v = get_argument (line, "--random_select=")
    if v is not None:
      config_name += "_rsel=" + str ( v )
      config_dic['rsel'] = v

    v = get_argument (line, "--select_exp=")
    if v is not None:
      config_name += "_selExp=" + str ( v )
      config_dic['selExp'] = v

    v = get_argument (line, "--card_wtrule=")
    if v is not None:
      config_name += "_cWtRl=" + str ( v )
      config_dic['cWtRl'] = v

    v = get_argument (line, "--maxs_inner_bound=")
    if v is not None:
      config_name += "_inb=" + str ( v )
      config_dic['inb'] = v

    v = get_argument (line, "--maxs_hit_bound=")
    if v is not None:
      config_name += "_hitb=" + str ( v )
      config_dic['hitb'] = v

    v = get_argument (line, "--maxs_inner_mult=")
    if v is not None:
      config_name += "_inMult=" + str ( v )
      config_dic['inMult'] = v

    v = get_argument (line, "--maxs_outer_restart=")
    if v is not None:
      config_name += "_outRes=" + str ( v )
      config_dic['outRes'] = v

    v = get_argument (line, "--hard_stochastic_selection=")
    if v is not None:
      config_name += "_hardSel=" + str ( v )
      config_dic['hardSel'] = v

    v = get_argument (line, "--maxs_flip_step=")
    if v is not None:
      config_name += "_flipStep=" + str ( v )
      config_dic['flipStep'] = v

    v = get_argument (line, "--init_clause_weight=")
    if v is not None:
      config_name += "_initCls=" + str ( v )
      config_dic['initCls'] = v

    v = get_argument (line, "--clsselectp=")
    if v is not None:
      config_name += "_selectRandCls=" + str ( v )
      config_dic['_selectRandCls'] = v
    
    if "--maxs_transfer_slow=1" in line:
      config_name += "_tslow"

    if "--maxs_transfer_slow=0" in line:
      config_name += "_tfast"

    if "--maxs_hard_takes_soft=0" in line:
      config_name += "_Nhtks"

    if "--neighbors_plus=1" in line:
      config_name += "_neigh"
    if "--ignorewtcriteria=1" in line:
      config_name += "_ignr"

    if "--maxs_transfer_soft=1" in line:
      config_name += "_softTrans"

    if "--maxs_soft_takes_hard=1" in line:
      config_name += "_stkh"

    # if "--maxtries=100" in line:
    #   config_name += "restart=100"
    # elif "--maxtries=1" in line:
    #   config_name += "restart=1"


  elif "solvers/ddfw" in line:
    solver = "ddfw"
    config_name += "ddfw"
  elif "solvers/yalsat" in line:
    solver = "yalsat"
    config_name += "yalsat"
  elif "solvers/cadical" in line:
    solver = "cadical"
    config_name += "cadical"
  elif "solvers/card_cadical" in line:
    solver = "card_cadical"
    config_name += "card_cadical"
  elif "solvers/CarlSAT" in line:
    solver = "CarlSAT"
    config_name += "CarlSAT"

  # get formula
  tokens = line.split()
  for i in range(len(tokens)):
    token = tokens[i]
    temp_formula = get_formula (token)
    if temp_formula[-3:] == "knf" or temp_formula[-3:] == "cnf" or temp_formula[-3:] == "ard":
      formula = temp_formula
  
  # get seed 
  if solver == "CarlSAT":
    for i in range(len(tokens)):
        token = tokens[i]
        if token == "-s":
          seed = int (tokens[i+1])
          break
  elif solver in ["yalsat", "ddfw", "card_ddfw"]:
    seed = int (tokens[-1])

  # print((solver,formula))
  if solver is None or formula is None: 
    print ("error, failed to find solver or formula")
    print (line)
    exit (1)

  config_dic['seed'] = seed
  config_dic['solver'] = solver
  config_dic['config_name'] = config_name
  config_dic['formula'] = formula

  return config_dic

# get time based on 'time' command
#  e.g.,
#   real	0m3.236s
#   user	0m3.227s
#   sys	0m0.009s
def get_time (line):
  total_time = 0.0
  minutes = 0
  seconds = 0.0
  tokens = line.split()
  chunk = tokens[1]

  temp_s = ""
  for c in chunk:
    if c == 'm':
      minutes = int (temp_s)
      temp_s = ""
    elif c == 's':
      seconds = float (temp_s)
    else :
      temp_s += c

  total_time = minutes * 60 + seconds

  return total_time

'''
Example,
c new minimum : nunsat best 0 (tmp 0), clauses 5645, constraints 0, flips 3098, 1.12 sec, 2.78 kflips/sec
c   weights best 1103131.000000 (tmp 1103131.000000), clauses 1103131.000000, constraints 0.000000
c   soft clauses 5645, constraints 0
'''
def get_min_cost_data (line1,line2,line3):
  d = {}
  tokens1 = line1.split()
  tokens2 = line2.split()
  tokens3 = line3.split()
  d['time'] = float (tokens1[15])
  d['cost'] = float (tokens2[3])
  d['soft clauses'] = int (tokens3[3][:-1])
  d['flips'] = int (tokens1[14][:-1])
  return d

'''
Example
1,040,911,

return 1040911
'''
def commas_to_num (line) :
  n = ""
  for c in line:
    if c == ',': continue
    n += c

  return int (n)

'''
Example,
c new cost after 10,974,844 flips (3436.165 secs) is 1,040,911, phaseI_flips = 1
'''
def get_min_cost_carl (line):
  d = {}
  tokens = line.split()
  d['time'] = float (tokens[6][1:])
  d['cost'] = commas_to_num (tokens[9])
  d['flips'] = commas_to_num (tokens[4])
  return d


def parse_log (log_file):
  data = {}
  with open(log_file) as ifile :
    lines = [line.rstrip() for line in ifile]

    next_configuration = False
    solver = None
    
    curr_data = {'flips':'-', 'kflips_ps':'-', 'final_min':'-', 'result':'unknown'}
    curr_config = None
    config_name = None
    list_configs = []
    formulas = []

    cntMissed = 0

    # loop over each line
    for line_n in range(len(lines)):
      line = lines[line_n]
      tokens = line.split()

      if len(tokens) == 0: continue
      elif next_configuration:
        # get current configuration info
        curr_config = get_configuration (line)
        config_name = curr_config['config_name']
        next_configuration = False
      elif "NEXT CONFIGURATION" in line:
        next_configuration = True
      elif "END CONFIGURATION" in line:
        if config_name not in data:
          list_configs.append (config_name)
          data[config_name] = {}
        # print(config_name)
        # Key for each configuation is formula and seed.
        # Nothing else should be necessary to differentiate
        # runs.
        dkey = (curr_config['formula'],curr_config['seed'])
        if dkey in data[config_name]:
          cntMissed += 1
          if data[config_name][dkey]['min cost'] < curr_data['min cost']:
            print("better one")
            curr_data['min cost'] = data[config_name][dkey]['min cost']
            curr_data['min cost list'] = data[config_name][dkey]['min cost list']
          # print ("error, dkey already exists")
          # print(dkey)
          # print((config_name, data[config_name].keys()))
          # print(data.keys())
          # print(curr_config['config_line'])
          # exit (1)

        if curr_config['solver'] == "CarlSAT":
          curr_data['flips'] = curr_data['min cost list'][-1]['flips']

        # add into main data dictionary
        curr_data['solver'] = curr_config['solver']
        curr_data['config_map'] = curr_config
        data[config_name][dkey] = curr_data

        if curr_config['formula'] not in formulas:
          formulas.append (curr_config['formula'])
        
        # reset current values until next configuration is parsed
        curr_data = {'flips':'-', 'kflips_ps':'-', 'final_min':'-', 'result':'unknown'}
        curr_config = None
        config_name = None
      elif tokens[0] == "real":
        curr_data['real'] = get_time (line)
      elif tokens[0] == "user":
        curr_data['user'] = get_time (line)
      elif "s SATISFIABLE" in line :
        curr_data['result'] = "sat"
      elif "s UNKNOWN" in line :
        curr_data['result'] = "unknown"
      elif "c UNKNOWN" in line :
        curr_data['result'] = "unknown"
      elif "s CURRENT BEST" in line :
        curr_data['result'] = "unknown"
      elif "final minimum " in line:
        curr_data['final_min'] = int(tokens[4])
      elif "minimum constraints " in line:
        curr_data['min clauses'] = int(tokens[3])
        curr_data['min constraints'] = int(tokens[6])
      elif len(tokens) > 3 and tokens[2] == "flips,":
        curr_data['flips'] = int(tokens[1])
        curr_data['kflips_ps'] = float(tokens[3])
      elif len(tokens) > 3 and tokens[1] == "Cost" and tokens[2] == "best":
        curr_data['min cost'] = float(tokens[3])
      elif len(tokens) > 3 and tokens[1] == "new" and tokens[2] == "cost":
        if 'min cost list' not in curr_data:
          curr_data['min cost list'] = []
        min_c = get_min_cost_carl (line)
        curr_data['min cost list'].append(min_c)
      elif len(tokens) > 6 and tokens[1] == "Solution" and tokens[5] == "cost":
        curr_data['min cost'] = float(commas_to_num(tokens[6][1:-1]))
      elif len(tokens) > 3 and tokens[1] == "new" and tokens[2] == "minimum" and tokens[4] == "nunsat":
        # print(line)
        if 'min cost list' not in curr_data:
          curr_data['min cost list'] = []
        min_c = get_min_cost_data (line, lines[line_n+1],lines[line_n+2])
        curr_data['min cost list'].append(min_c)
  
  
  print(cntMissed)
  return data, formulas

def parse_csv (csv_file) :
  d = {}
  formulas = []
  with open(csv_file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      # print(line)
      entry = {}
      if line["formula"] not in formulas:
        formulas.append (line["formula"])
      c = line["config"]
      if c not in d:
        d[c] = {}
      dkey = (line["formula"], line["seed"])
      if dkey in d[c]:
        print ("repeated config and seed on formula")
        exit (1)
      entry['solver'] = line['solver']
      entry['flips'] = int (line['flips'])
      if 'min cost' in line:
        entry['min cost'] = float (line['min cost'])
      else:
        entry['min cost'] = float (line['min-cost'])

      entry['config_map'] = {}

      k_exp = get_argument_t (c.split("_"), "ex=")
      entry['config_map']['k_exp'] = k_exp

      init_card = get_argument_t (c.split("_"), "initCard=")
      entry['config_map']['init_card'] = init_card

      t_all = get_argument_t (c.split("_"), "tall=")
      entry['config_map']['t_all'] = t_all

      sel = get_argument_t (c.split("_"), "select=")
      entry['config_map']['stoch_sel'] = sel

      v = get_argument_t (c.split("_"), "rsel=")
      entry['config_map']['rsel'] = v

      v = get_argument_t (c.split("_"), "select=")
      entry['config_map']['stoch_sel'] = v

      v = get_argument_t (c.split("_"), "selExp=")
      entry['config_map']['selExp'] = v

      v = get_argument_t (c.split("_"), "cWtRl=")
      entry['config_map']['cWtRl'] = v

      v = get_argument_t (c.split("_"), "inb=")
      entry['config_map']['inb'] = v

      v = get_argument_t (c.split("_"), "hitb=")
      entry['config_map']['hitb'] = v

      v = get_argument_t (c.split("_"), "inMult=")
      entry['config_map']['inMult'] = v

      v = get_argument_t (c.split("_"), "flipStep=")
      entry['config_map']['flipStep'] = v

      v = get_argument_t (c.split("_"), "outRes=")
      entry['config_map']['outRes'] = v

      v = get_argument_t (c.split("_"), "hardSel=")
      entry['config_map']['hardSel'] = v

      v = get_argument_t (c.split("_"), "_selectRandCls=")
      entry['config_map']['_selectRandCls'] = v

      init_cls = get_argument_t (c.split("_"), "initCls=")
      entry['config_map']['init_cls'] = init_cls

      entry['min cost list'] = {}

      if dkey in d[c]:
        if d[c][dkey]['min cost'] < entry['min cost']:
          entry['min cost'] = d[c][dkey]['min cost']

      d[c][dkey] = entry
      # print(entry)

  return d, formulas


def get_cost (formula, cost) :
  n = 0
  if formula == "mm-SR03.wknf" or formula == "mm-SR03.wcard":
    n = cost + 4249274
  elif formula == "mm-SR05.wknf" or formula == "mm-SR05.wcard":
    n = cost + 446694
  elif formula == "mm-SW02.wknf" or formula == "mm-SW02.wcard":
    n = cost + 2014818
  elif formula == "mm-SW05.wknf" or formula == "mm-SW05.wcard":
    n = cost + 237648
  return n

def get_percentage (formula, cost) :
  n = 0
  if formula == "mm-SR03.wknf" or formula == "mm-SR03.wcard":
    n = cost / 5256604.0
  elif formula == "mm-SR05.wknf" or formula == "mm-SR05.wcard":
    n = cost / 1450176.0
  elif formula == "mm-SW02.wknf" or formula == "mm-SW02.wcard":
    n = cost / 2342652.0
  elif formula == "mm-SW05.wknf" or formula == "mm-SW05.wcard":
    n = cost / 605067.0
  return n * 100.0

def run(name, args):

  input_file = None
  print_mins = False
  csv_file = None

  colorsAll = ['redpurple','lightblue','darkbrown','clearorange','darkpurple','mildgray','bluegray','lightgreen','redpurple','clearyellow','clearpurple','browngreen','darkestpurple','greypurple','darktruqoise','midblue','midgreen','darkred','softblue','darkestblue','lightpurple','softgreen','darkestblue']
  colorsCnt = 23
  marksAll = ['+','x','Mercedes star','Mercedes star flipped','|','-','star']#,'diamond', "square",'o']
  marksCnt = 5

  colors = colorsAll 
  marks = marksAll

  opts, args = getopt.getopt(args, "mi:c:")

  for (opt,value) in opts:
    if (opt == '-i'):
      input_file = value
    if (opt == '-m'):
      print_mins = True
    if (opt == '-c'):
      csv_file = value


  data = {}
  formulas = []
  if input_file is not None:
    data,formulas = parse_log (input_file)

  if csv_file is not None:
    data,formulas = parse_csv (csv_file)
      
  # print(data)
  if (print_mins):
    # print min cost over time based on list provided (assuming times given by solvers are correct...)
    seed_best = {}

    exp_best = {} # best for each exponent
    sel_best = {}

    gen_best = [{},{}]
    gen_name = 'init_card'
    neigh = 0
    time_cutoff = 2700

    config_best = {}

    max_percent_cutoff = 106 # anything above this is chopped
    # max_percent_cutoff = 300

    for formulaP in formulas:
      # print(formulaP)
      for config_name in data.keys():
        # if "tslow" in config_name : continue
        # if "ex" in config_name : continue
        

        for (formula, seed) in data[config_name].keys():
          if (formula != formulaP) : continue
          d = data[config_name][(formula, seed)]
          # if d['flips'] == '-': continue
          # if d['config_map']['hitb'] == 10 : continue
          # if d['config_map']['stoch_sel'] != 3 : continue
          # if "outRes" in d['config_map'] : continue
          if d['config_map']['hitb'] != 1 : continue
          if d['config_map']['_selectRandCls'] != 12 : continue
          if d['config_map']['init_card'] != 35 : continue

          ## General Min cast
          if not 'min cost list' in data[config_name][(formula, seed)]:
            print(data)
            print(data[config_name][(formula, seed)])

          min_list = data[config_name][(formula, seed)]['min cost list']
          
          prev = 0
          for ml in min_list:
            t = ml['time']
            cost = ml['cost']
            if t > time_cutoff: break
            prev = cost
          d['min cost'] = prev

          ## standard seed best for each formula
          ##
          if formula in seed_best:
            if d['min cost'] < seed_best[formula][0]:
              seed_best[formula] = (d['min cost'],config_name,seed)
          else:
            seed_best[formula] = (d['min cost'],config_name,seed)
          if d['flips'] == '-':
            d['flips'] = d['min cost list'][-1]['flips']



          ## best for each config
          if 'outRes' in d['config_map']: continue

          if formula not in config_best:
            config_best[formula] = {}
          if config_name not in config_best[formula]:
            config_best[formula][config_name] = (d['min cost'],config_name,seed)
          else:
            if d['min cost'] < config_best[formula][config_name][0]:
              config_best[formula][config_name] = (d['min cost'],config_name,seed)


          ## gen best seed
          ##
          ## Filter
          if gen_name not in d['config_map']: # filter non-experiments
            continue
          if d['config_map'][gen_name] is None:
            continue
          
          # if "stoch_sel" in d['config_map'] and d['config_map']["stoch_sel"] != 2: continue
          # if "hitb" in d['config_map'] and d['config_map']["hitb"] != 10: continue
          # if 'selExp' in d['config_map'] and d['config_map']['selExp'] != 10051 : continue
          # if 'init_card' in d['config_map']: continue
          # if 'init_card' not in d['config_map'] or d['config_map']['init_card'] != 5: continue
          
          if '_neigh' in config_name: # filter "good" configuration
            neigh = 1
          else : neigh = 0
          ## Get value
          if formula not in gen_best[neigh]:
            gen_best[neigh][formula] = {}
          val = d['config_map'][gen_name]
          if val in gen_best[neigh][formula]:
            if d['min cost'] < gen_best[neigh][formula][val][0]:
              gen_best[neigh][formula][val] = (d['min cost'],config_name,seed)
          else:
            gen_best[neigh][formula][val] = (d['min cost'],config_name,seed)


    ## Print best scores for general (OLD)
    ##
    # cnt = 0
    # # for neigh in range(2):
    # for neigh in [1]:
    #   for formula in ["mm-SR03.wknf", "mm-SR05.wknf"]:
    #   # for formula in ["mm-SW02.wknf", "mm-SW05.wknf"]:
    #     print( add_line_prefix (colors[cnt],marks[cnt],None,None))
    #     for val in range(-6,16,1):
    #       (b,c,s) = gen_best[neigh][formula][val]
    #       # print ((add_point (val,b)) + " ")
    #       print ((add_point (val/10.0 + 1,b)) + " ")
    #     print(add_end_line())
    #     cnt += 1

    ## Print best scores for general
    ##
    # cnt = 0
    # # for neigh in range(2):
    # for neigh in [1]:
    #   for formula in ["mm-SR03.wknf", "mm-SR05.wknf"]:
    #   # for formula in ["mm-SW02.wknf", "mm-SW05.wknf"]:
    #     print( add_line_prefix (colors[cnt],marks[cnt],None,None))
    #     for val in range(2,10,1):
    #       (b,c,s) = gen_best[neigh][formula][val]
          
    #       n = get_cost (formula, b)
    #       p = get_percentage (formula, n)
    #       # print ((add_point (val/10.0 + 1,p)) + " ")
    #       print ((add_point (val,p)) + " ")
    #     print(add_end_line())
    #     cnt += 1

    ## Print best scores for general (Min Cost)
    # ##
    cnt = 0
    legend = []
    dashed_tails = []
    n = None 
    p = None
    lastTime = 0
    endXaxis = 3000
    
    # for neigh in range(2):
    for neigh in [1]:
      for formula in ["mm-SR03.wknf", "mm-SR05.wknf", "mm-SW02.wknf", "mm-SW05.wknf"]:
      # for formula in ["mm-SR03.wcard", "mm-SR05.wcard", "mm-SW02.wcard", "mm-SW05.wcard"]:
        # f = open(gen_name+"_noNeigh_"+formula[:-5]+".tex", 'w')
        f = open(gen_name+"_"+formula[:-5]+".tex", 'w')
        cnt = -1
        dashed_tails = []

        f.write (add_tikz_header())
        f.write (add_plot_header (gen_name+formula,"time (s)",0,endXaxis,None,None,None,formula))

        f.write (add_other_baselines (formula,2700,endXaxis))

        # f.write (add_plot_header (gen_name+formula,"time (s)",0,endXaxis,None,92,300,formula))

        ## CarlSAT
        # f = open("Carl_"+formula[:-6]+".txt", 'w')
        # d = seed_best[formula]
        # min_list = data[d[1]][(formula,d[2])]['min cost list']
        # # print(min_list)
        # f.write ( add_line_prefix ("red","star",None,0.5, None) + "\n")
        # for g in min_list :
        #   n = get_cost (formula, g['cost'])
        #   p = get_percentage (formula, n)
        #   f.write ((add_point (g['time'],p)) + " " + "\n") 
        #   lastTime = g['time']
        # f.write ((add_point (endXaxis,p)) + " " + "\n")  
        # f.write (add_end_line()  + "\n")

        ## General
        # f.write ( add_line_prefix (colorsAll[cnt],marksAll[cnt % marksCnt],None,0.5, None) + "\n")

        # print(formula)

        # first pass to sort
        legend = []
        sorted_vals = []
        # for val in range(60, 100, 2):
        #   (b,c,s) = gen_best[neigh][formula][val]
        #   sorted_vals.append((val,b))

        # sorted_vals.sort(key=lambda k: k[1], reverse=True)

        # for val,_ in sorted_vals:
        # # for val in  [100,250,500,750,1000,1250,1500,1750,2000]:
        #   cnt += 1
        #   # if val not in gen_best[neigh][formula]: print (val)
        #   (b,c,s) = gen_best[neigh][formula][val]



        ## Best Config
        # for val in config_best[formula].keys():
        #   cnt += 1
        #   (b,c,s) = config_best[formula][val]
        #   val = '-'.join(val.split('_'))

        ## Best overall
        for val in range(1):
          cnt += 1
          (b,c,s) = seed_best[formula]
          new_c = '-'.join(c.split('_')) 
          
          ## normal
          # n = get_cost (formula, b)
          # p = get_percentage (formula, n)
          # f.write ((add_point (val/10.0 + 1,p)) + " " + "\n")
          
          # print(val)
          # print(p)
          # print(((add_point (val/10.0 + 1,p)) + " " + "\n"))
          
          ## min cost
          min_list = data[c][(formula,s)]['min cost list']

          f.write ( add_line_prefix (colorsAll[cnt],marksAll[cnt % marksCnt],None,0.5, None) + "\n")

          for g in min_list :
            n = get_cost (formula, g['cost'])
            p = get_percentage (formula, n)
            if g['time'] > time_cutoff : break
            if p <= max_percent_cutoff:
              f.write ((add_point (g['time'],p)) + " " + "\n") 
              lastTime = g['time']
            
          if val not in legend: legend.append(val)
          f.write (add_end_line()  + "\n")
          dashed_line = add_line_prefix (colorsAll[cnt],None,None,None, None, 1)
          dashed_line += (add_point (lastTime,p)) + " " + (add_point (endXaxis+10,p))
          dashed_line += add_end_line()
          dashed_tails.append (dashed_line)

        for dashed_line in dashed_tails: f.write(dashed_line + "\n")

        
        f.write (add_dashed_line())
        f.write(add_legend (legend))

        f.write (add_plot_tail ())


        # f.write (add_end_line() + "\n")
        f.close()

    #table
    # for form in seed_best.keys():
    #   print("\n"+form+"\n")
    #   for ratio in [0.1, 0.4,0.5,0.6 ,0.8, 1]:
    #     print([10,20,40,80,160,320])
    #     s = str(ratio) + ": "
    #     for cls_weight in [10,20,40,80,160,320]:
    #       c = "card=Lin_initCard={}_inb=2000_hitb=10_inMult=125_hardSel=5_initCls={}_Nhtks_neigh".format(cls_weight, cls_weight*ratio)
    #       s += str(config_best[form][c][0]) + " "
    #     print(s)
    
    ## Print best scores for each formula
    ##   score modified with offset from wcard files (sum of units)
    for form in seed_best.keys():
      (b,c,s) = seed_best[form]
      print(form)
      n = get_cost (form, b)
      p = get_percentage (form, n)
      print((b,n,p,c,s))
      

    ## Tikz plot for specific formula
    # ##
    # f = "mm-SR03.wknf" # wknf for weight-transfer solver, wcard for carlsat
    # d = seed_best[f]
    # min_list = data[d[1]][(f,d[2])]['min cost list']
    # print( add_line_prefix ('softblue','x',None,None))
    # for g in min_list:
    #   print ((add_point (g['time'],g['cost'])) + " ") # time/flips
    # print(add_end_line())
    # print (seed_best[f])

  else:
    # write the data in csv fomrat
    # first write the complete header
    header = "{} {} {} {} {} {} {} {} {} {} {} {}".format("formula","config","solver","minimum","real","flips","kflips-per-sec","result","seed","min-clauses","min-constraints", "min-cost")
    
    print(header)

    # print data for each configuration
    # can sort by formulas in the csv
    for config_name in data.keys():
      for (formula, seed) in data[config_name].keys():
        d = data[config_name][(formula, seed)]
        line = "{} {} {} ".format(formula, config_name, d['solver'])


        # calculate kflips_ps by hand
        # messed up with solvers, need to flush time before printing stats when exiting
        if d['flips'] != '-':
          d['kflips_ps'] = (d['flips'] / 1000.0) / d['real']

        line += "{} {} {} {} ".format(d['final_min'], d['real'], d['flips'], d['kflips_ps'])

        if 'result' not in d: print(line)

        line += " {} {} ".format(d['result'], seed)

        if 'min constraints' in d:
          line += " {} {} ".format(d['min clauses'], d['min constraints'])
        else:
          line += " - - "

        if 'min cost' in d:
          line += " {}".format(d['min cost'])

        print(line)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])