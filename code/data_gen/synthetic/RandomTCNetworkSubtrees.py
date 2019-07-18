import copy
import random


###########################################
# PARSING


def find_nth(haystack, needle, n):
    start = haystack.find(needle)
    while start >= 0 and n > 1:
        start = haystack.find(needle, start+len(needle))
        n -= 1
    return start

def ParseTC(line):
    comma = line.find(',')
    sec_comma = find_nth(line, ',', 2)
    leaves = int(line[:comma])
    reticulations = int(line[comma + 1: sec_comma])
    samplesize = int(line[sec_comma + 1:])
    return [leaves, reticulations, samplesize]


# Changes all Newick trees with strings to Newick trees with integers

def ListIntegerizer(TCnetwork):
    if isinstance(TCnetwork[0], str) and isinstance(TCnetwork[1], str):
        TCnetwork[0] = int(TCnetwork[0])
        TCnetwork[1] = int(TCnetwork[1])
        return TCnetwork
    elif isinstance(TCnetwork[0], str):
        TCnetwork[0] = int(TCnetwork[0])
        if isinstance(TCnetwork[1], list):
            TCnetwork[1] = ListIntegerizer(TCnetwork[1])
        return TCnetwork
    elif isinstance(TCnetwork[1], str):
        TCnetwork[0] = ListIntegerizer(TCnetwork[0])
        if isinstance(TCnetwork[0], list):
            TCnetwork[1] = int(TCnetwork[1])
        return TCnetwork
    else:
        TCnetwork[0] = ListIntegerizer(TCnetwork[0])
        TCnetwork[1] = ListIntegerizer(TCnetwork[1])
    return TCnetwork



###########################################
# Preliminaries



# Finds all clusters (pendant subnetworks with split nodes as roots)
# of a tree. Used to find reticulations later.

def TreeClusterSet(tree, m):
    A = tree[0]
    B = tree[1]
    if isinstance(A,int) and isinstance(B,int):
        return m
    elif isinstance(A,int):
        m.append(B)
        TreeClusterSet(B, m)
        return m
    elif isinstance(B,int):
        m.append(A)
        TreeClusterSet(A, m)
        return m
    else:
        m.extend((A,B))
        TreeClusterSet(A, m)
        TreeClusterSet(B, m)
        return m



# Checks if A is contained in B.
# Generally, A is the reticulation edge and B the network.

def CheckIntersection(A, B):
    if A == B:
        return True
    elif ', ' + str(A) + ']' in str(B) or '[' + str(A) + ',' in str(B):
        return True
    return False


# Remove duplicate elements from a list
def RemoveDuplicates(tree):
    noduplicates = []
    for item in tree:
        if item not in noduplicates:
            noduplicates.append(item)
    return noduplicates


# Turns a list of lists into a tuple of tuples.

def deep_tuple(x):
    if type(x)!= type( [] ):
        return x
    return tuple(map(deep_tuple, x))



#################################################################
# Random TC Network construction


# Returns a list of all leaves in the tree/network.
def Leaves(tree, leaves):
    if isinstance(tree, int):
        if tree not in leaves:
            leaves.append(tree)
        return leaves
    else:
        Leaves(tree[0], leaves)
        Leaves(tree[1], leaves)
        return leaves


# From Remie's, finds all cherries in a tree / TC network.
def CherryListTree( tree ):
    if type(tree) == int:
        return []
    if len(tree)==2:
        if type(tree[0])==int and type(tree[1])==int:
            return [[tree[0],tree[1]],[tree[1],tree[0]]]
        elif type(tree)==list:
            return CherryListTree(tree[0]) +CherryListTree(tree[1])
    else:
        return []



#Replaces every occurrence of cluster A in tree by cluster B.

def Replace(tree, A, B):
    if A in tree:
        Bcopy = copy.deepcopy(B)
        if A == tree[0]:
            tree[0] = B
            if CheckIntersection(A, tree[1]):
                tree[1] = Replace(tree[1], A, Bcopy)
        else:
            tree[1] = B
            if CheckIntersection(A, tree[0]):
                tree[0] = Replace(tree[0], A, Bcopy)
    else:

        if CheckIntersection(A, tree[0]):
            Bcopy = copy.deepcopy(B)
            tree[0] = Replace(tree[0], A, Bcopy)

        if CheckIntersection(A, tree[1]):
            Bcopy = copy.deepcopy(B)
            tree[1] = Replace(tree[1], A, Bcopy)
    return tree



# Randomly selects a leaf and expands.
# The leaf is removed from noret if it was contained in it.
def Split(tree, noret):
    leaves = sorted(Leaves(tree, []))
    validret = [item for item in leaves if item not in noret]
    splitnode = random.choice(leaves)
    if splitnode != leaves[-1]:
        for i in reversed(range(splitnode + 1, len(leaves) + 1)):
            Replace(tree, i, i+1)
            if i in noret:
                noret.remove(i)
                noret.append(i+1)
    ListaAux = []
    ListaAux = [splitnode, splitnode + 1]
    Replace(tree, splitnode, ListaAux )
    if splitnode in noret:
        noret.remove(splitnode)
    if splitnode+1 in noret:
        noret.remove(splitnode+1)
    noret = RemoveDuplicates(noret)
    return [tree, noret]


# Finds all leaves that are in cherries with the reticulation parents, and adds them to noret.
# This is to prevent the W shapes.
def CherryPairs(cherries, retparents, noret):
    noretnodup = []
    noretadjust = []
    for cherry in cherries:
        for node in retparents:
            if node in cherry:
                if node == cherry[0]:
                    noret.append(cherry[1])
                else:
                    noret.append(cherry[0])
    for item in noret:
        if item not in noretnodup:
            noretnodup.append(item)
    noret = noretnodup
    for item in noret:
        if item > retparents[1]:
            noretadjust.append(item - 1)
        else:
            noretadjust.append(item)
    noret = noretadjust
    return noret



# Returns a network after having undergone a reticulation, where the retparents are the parents of the reticulation.
# noret, the set of all leaves that cannot be in a reticulation, is updated.
def Reticulation(tree, noret):
    leaves = sorted(Leaves(tree, []))
    validret = [item for item in leaves if item not in noret]
    retparents = random.sample(validret, 2)
    while retparents in CherryListTree(tree):
        retparents = random.sample(validret, 2)
    retparents = sorted(retparents, key=int)
    noret.append(retparents[0])
    noret = CherryPairs(CherryListTree(tree), retparents, noret)
    if retparents[1] != leaves[-1]:
        Replace(tree, retparents[1], retparents[0])
        for i in range(retparents[1] + 1, len(leaves) + 1):
            Replace(tree, i, i-1)
    else:
        Replace(tree, retparents[1], retparents[0])
    return [tree, noret]



# Generates a random TC network with n leaves and possibly fewer than k reticulations.
def GenerateTCNetwork(n, k):
    if n == 1:
        return [1]
    tree = [1,2]
    remaining_split = n+k-2
    remaining_ret = k
    leaves = [1,2]
    validret = [1,2]
    noret = []

    while not (remaining_split == 0 and remaining_ret == 0):
        if remaining_ret == 0:
            [tree, noret] = Split(tree, noret)
            remaining_split -= 1
        elif remaining_split == 0:
            validret = [item for item in sorted(Leaves(tree, [])) if item not in noret]
            if (len(validret) == 2 and validret in CherryListTree(tree)) or len(validret) < 2 or len(Leaves(tree,[])) == 2:
                remaining_ret = 0
            else:
                [tree, noret] = Reticulation(tree, noret)
                remaining_ret -= 1
        else:
            chosen_node = random.randint(1, remaining_split + remaining_ret)
            validret = [item for item in sorted(Leaves(tree, [])) if item not in noret]
            if chosen_node <= remaining_split or (len(validret) == 2 and validret in CherryListTree(tree)) or len(validret) < 2 or len(Leaves(tree,[])) == 2:
                [tree, noret] = Split(tree, noret)
                remaining_split -= 1
            else:
                [tree, noret] = Reticulation(tree, noret)
                remaining_ret -= 1
    return tree



#################################################################
# Edge Deletion

# Sorts reticulations by their size
# in terms of number of characters.

def SortByStringSize(retlist):
    return len(str(retlist))



# Finds all reticulations of the network

def FindReticulations(network):
    reticulation = []
    retnoduplicate = []
    retlist = []
    retint = []
    cluster = TreeClusterSet(network, [network])
    for item in cluster:
       for item2 in cluster:
           if item != item2:
                if isinstance(item, list) and isinstance(item, list):
                    for item3 in item:
                        if item3 in item2:
                            reticulation.append(item3)
                elif isinstance(item, int) and isinstance(item2, list):
                        if item in item2:
                            reticulation.append(item)
                elif isinstance(item2, int) and isinstance(item, list):
                    if item2 in item:
                        reticulation.append(item2)
    for item4 in reticulation:
        if item4 not in retnoduplicate:
            retnoduplicate.append(item4)
    for item5 in retnoduplicate:
        if not isinstance(item5, int):
            retlist.append(item5)
        if isinstance(item5, int):
            retint.append(item5)
    retlist.sort(key = SortByStringSize, reverse=True)
    for item6 in retint:
        retlist.append(item6)
    return retlist



# Deletes a specified reticulation from a network,
# given the network only contains one of the reticulation edges.

def GetRidOf(network, edge):
    if edge in network:
        network.remove(edge)
        return network[0]
    elif CheckIntersection(edge, network[0]):
        network[0] = GetRidOf(network[0], edge)
        return network
    elif CheckIntersection(edge, network[1]):
        network[1] = GetRidOf(network[1], edge)
        return network



# Deletes a specified reticulation from a network
# and returns two subnetworks, one for each reticulation edge.

def EdgeDeletionRandom(network, edge):
    copynetwork0 = copy.deepcopy(network[0])
    copynetwork1 = copy.deepcopy(network[1])
    copyedge = copy.deepcopy(edge)
    subtree = []
    if CheckIntersection(edge, network[0]) and CheckIntersection(edge, network[1]):
        value = random.uniform(0, 1)
        if edge == network[0]:
            if edge in network[1]:
                return [copynetwork1]
            else:
                if value < 0.5:
                    return [copynetwork1]
                else:
                    return [[copyedge, GetRidOf(copynetwork1, edge)]]
        elif edge == network[1]:
            if edge in network[0]:
                return [copynetwork0]
            else:
                if value < 0.5:
                    return [[GetRidOf(copynetwork0, edge), copyedge]]
                else:
                    return [copynetwork0]
        else:
            if value < 0.5:
                return [[GetRidOf(copynetwork0, edge), copynetwork1]]
            else:
                return [[copynetwork0, GetRidOf(copynetwork1, copyedge)]]
    elif CheckIntersection(edge, network[0]):
        for item in EdgeDeletionRandom(copynetwork0, edge):
            subtree.append([item, copynetwork1])
        return subtree
    elif CheckIntersection(edge, network[1]):
        for item in EdgeDeletionRandom(copynetwork1, edge):
            subtree.append([copynetwork0, item])
        return subtree



# Returns a tuple of all displayed subtrees
# of a tree-child network.

def AllSubtree(network):
    copynetwork = copy.deepcopy(network)
    subtree = [copynetwork]
    if FindReticulations(network) != []:
        for ret in FindReticulations(network):
            subtree2 = []
            subtree3 = []
            for net in subtree:
                for item in EdgeDeletionRandom(net, ret):
                    subtree3.append(item)
            for item in subtree3:
                if item not in subtree2:
                    subtree2.append(item)
            subtree = subtree2
        return subtree2
    else:
        return subtree


def RandomSubtrees(network, s):
    subtrees = []
    count = 0
    error_message = ''
    while s != 0:
        tree = AllSubtree(network)[0]
        if tree not in subtrees:
            subtrees.append(tree)
            s -= 1
        else:
            count += 1
            if count < 100:
                continue
            else:
                error_message = 'this network does not have ' + str(s) + ' many different subtrees.'
                return [deep_tuple(subtrees), error_message, len(subtrees)]
    return [deep_tuple(subtrees), error_message, len(subtrees)]


######################################################
# Putting it all together

#==============================================================================
# 
# input =   open('input.txt', 'r')
# output =  open('RandomTCsubtrees.txt', 'w')
# output2 = open('RandomTCdescription.txt', 'w')
# 
# for line in input:
#     [leaves, reticulations, samplesize] = ParseTC(line)
#     if leaves <= reticulations:
#         error
#     if samplesize > 2**reticulations:
#         error
#     network = GenerateTCNetwork(leaves, reticulations)
#     while max(Leaves(network, [])) != leaves:
#         network = GenerateTCNetwork(leaves, reticulations)
#     reticulations = len(FindReticulations(network))
#     [subtrees, error_message, actualsamplesize] = RandomSubtrees(network, samplesize)
#     output2.write('Number of leaves:' + str(leaves))
#     output2.write('\n')
#     output2.write('Number of reticulations:' + str(reticulations))
#     output2.write('\n')
#     output2.write('Number of subtrees in other output file:' + str(actualsamplesize))
#     output2.write('\n')
#     output2.write('The tree-child network is:' + str(deep_tuple(network)) + ';')
#     output2.write('\n')
#     if error_message != '':
#         output2.write('ERROR MESSAGE: ' + error_message)
#     output2.close()
#     for tree in subtrees:
#         treestring = str(tree) + ';'
#         if tree == subtrees[-1]:
#             output.write(treestring.replace(' ', ''))
#         else:
#             output.write(treestring.replace(' ', ''))
#             output.write('\n')
#     output.close()
# input.close()
# 
#==============================================================================
