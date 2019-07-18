import sys
from RandomTCNetworkSubtrees import *


def RandomTrees(n,k,t):
    nw=GenerateTCNetwork(n, k)
    trees = RandomSubtrees(nw, t)[0]
    return trees

def TreeToNewick(tree):
    if type(tree)!=list:
        return str(tree)
    newick="("
    for t in tree:
        newick+=TreeToNewick(t)+","
    return newick[:-1]+")"


option_k = False
option_k_argument = 0
option_t = False
option_t_argument = 2
option_n = False
option_n_argument = 10
i = 1

while i < len(sys.argv):
    arg= sys.argv[i]
    if arg == "-k":
        option_k = True
        i+=1
        option_k_argument = int(sys.argv[i])
    if arg == "-t":
        option_t = True
        i+=1
        option_t_argument = int(sys.argv[i])
    if arg == "-n":
        option_n = True
        i+=1
        option_n_argument = int(sys.argv[i])
    i += 1
    
rngTrees=RandomTrees(option_n_argument,option_k_argument,option_t_argument)    
for t in rngTrees:
    print( TreeToNewick(t)+str(";"))
