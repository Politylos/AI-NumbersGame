'''

In the Letters and Numbers (L&N) game,
One contestant chooses how many "small" and "large" numbers they would like 
to make up six randomly chosen numbers. Small numbers are between 
1 and 10 inclusive, and large numbers are 25, 50, 75, or 100. 
All large numbers will be different, 
so at most four large numbers may be chosen. 


How to represent a computation?

Let Q = [q0, q1, q2, q3, q4, q5] be the list of drawn numbers

The building blocks of the expression trees are
 the arithmetic operators  +,-,*
 the numbers  q0, q1, q2, q3, q4, q5

We can encode arithmetic expressions with Polish notation
    op arg1 arg2
where op is one of the operators  +,-,*

or with expression trees:
    (op, left_tree, right_tree)
    
Recursive definition of an Expression Tree:
 an expression tree is either a 
 - a scalar   or
 - a binary tree (op, left_tree, right_tree)
   where op is in  {+,-,*}  and  
   the two subtrees left_tree, right_tree are expressions trees.

When an expression tree is reduced to a scalar, we call it trivial.


Author: f.maire@qut.edu.au

Created on April 1 , 2021
    

This module contains functions to manipulate expression trees occuring in the
L&N game.

'''

from functools import lru_cache
from math import ceil, floor
import numpy as np
import random
import copy # for deepcopy
import collections
import re
import time

SMALL_NUMBERS = set(range(1,11))
LARGE_NUMBERS = (25, 50, 75, 100)
OPERATORS = ('*','+','-')
INT_MAX = np.iinfo(np.int32).max

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

def my_team():
    '''
    Return the list of the team members of this assignment submission as a list
    of triplet of the form (student_number, first_name, last_name)
    
    '''
    return [ (10582835, 'Thomas', 'Fabian'), (10489045, 'Sofia', 'Politylos') ]

# ----------------------------------------------------------------------------

def pick_numbers():
    '''    
    Create a random list of numbers according to the L&N game rules.
    
    Returns
    -------
    Q : int list
        list of numbers drawn randomly for one round of the game
    '''
    LN = set(LARGE_NUMBERS)
    Q = []
    for i in range(6):
        x = random.choice(list(SMALL_NUMBERS)+list(LN))
        Q.append(x)
        if x in LN:
            LN.remove(x)
    return Q

# ----------------------------------------------------------------------------

def bottom_up_creator(Q):
    '''
    Create a random algebraic expression tree
    that respects the L&N rules.
    
    Warning: Q is shuffled during the process

    Parameters
    ----------
    Q : non empty list of available numbers
        

    Returns  T, U
    -------
    T : expression tree 
    U : values used in the tree

    '''
    n = random.randint(1,6) # number of values we are going to use
    
    random.shuffle(Q)
    # Q[:n]  # list of the numbers we should use
    U = Q[:n].copy()
    
    if n==1:
        # return [U[0], None, None], [U[0]] # T, U
        return U[0], [U[0]] # T, U
        
    F = [u for u in U]  # F is initially a forest of values
    # we start with at least two trees in the forest
    while len(F)>1:
        # pick two trees and connect then with an arithmetic operator
        random.shuffle(F)
        op = random.choice(OPERATORS)
        T = [op,F[-2],F[-1]]  # combine the last two trees
        F[-2:] = [] # remove the last two trees from the forest
        # insert the new tree in the forest
        F.append(T)
    # assert len(F)==1
    return F[0], U

# ---------------------------------------------------------------------------- 

def display_tree(T, indent=0):
    '''
    
    Eval the algebraic expression represented by T
    
    Parameters
    ----------
    T : Expression Tree
    indent: indentation for the recursive call

    Returns None

    '''
    # if T is a scalar, then we return it directly
    if isinstance(T, int):
        print('|'*indent,T, sep='')
        return
    # T is non trivial
    root_item = T[0]
    print('|'*indent, root_item, sep='')
    display_tree(T[1], indent+1)
    print('|'*indent)
    display_tree(T[2], indent+1)
   
# ---------------------------------------------------------------------------- 

def eval_tree(T):
    '''
    
    Eval the algebraic expression represented by T
    
    Parameters
    ----------
    T : Expression Tree

    Returns
    -------
    value of the algebraic expression represented by the T

    '''
    # if T is a scalar, then we return it directly
    if isinstance(T, int):
        return T

    if len(T) == 1:
        return T[0]

    # T is non trivial
    root_item = T[0]
    # assert root_item in ('-','+','*')
    left_value = eval_tree(T[1])
    right_value = eval_tree(T[2])
    return eval( str(left_value) +root_item + str(right_value) )
    # return eval(root_item.join([str(left_value), str(right_value)]))
   
     
# ---------------------------------------------------------------------------- 

def expr_tree_2_polish_str(T):
    '''
    Convert the Expression Tree into Polish notation

    Parameters
    ----------
    T : expression tree

    Returns
    -------
    string in Polish notation represention the expression tree T

    '''
    if isinstance(T, int):
        return str(T)
        
    root_item = T[0]
    # assert root_item in ('-','+','*')
    left_str = expr_tree_2_polish_str(T[1])
    right_str = expr_tree_2_polish_str(T[2])
    return '[' + ','.join([root_item,left_str,right_str]) + ']'
    
# ----------------------------------------------------------------------------

def polish_str_2_expr_tree(pn_str):
    '''
    Convert a polish notation string of an expression tree
    into an expression tree T.

    Parameters
    ----------
    pn_str : string representing an L&N algebraic expression

    Returns
    -------
    T

    '''

    ''' 
    Recursive Regex pattern:

    str = ['+',3,['-',['+',6,['+',9,5]],['+',8,10]]]

    # str children
    O = '+'
    L = 3
    R = ['-',['+',6,['+',9,5]],['+',8,10]]
        O = '-'
        L = ['+',6,['+',9,5]]
            O = '+'
            L = 6
            R = ['+',9,5]
                O = '+'
                L = 9
                R = 5
        R = ['+',8,10]
            O = '+'
            L = 8
            R = 10 
    '''

    # Pre-compile regex pattern for faster iterations
    pattern = re.compile(r"'?([\*\-\+])'?,(\[.*\]|\d*),(\[.*\]|\d*)")

    def search_rec(str):
        # If child is a digit, just return it
        if str.isdigit():
            return int(str)

        # Execute regex pattern to separate nested children
        N = pattern.search(str)
        operator = N.group(1)
        lchild = search_rec(N.group(2))
        rchild = search_rec(N.group(3))

        # Return nodes as array
        return [ operator, lchild, rchild ]

    # Remove whitespace from string and call recursive function
    return search_rec(pn_str.replace(' ', ''))
   
# ----------------------------------------------------------------------------

def op_address_list(T, prefix = None):
    '''
    Return the address list L of the internal nodes of the expresssion tree T
    
    If T is a scalar, then L = []

    Note that the function 'decompose' is more general.

    Parameters
    ----------
    T : expression tree
    prefix: prefix to prepend to the addresses returned in L

    Returns
    -------
    L
    '''
    if isinstance(T, int):
        return []
    
    if prefix is None:
        prefix = []
        
    L = [prefix.copy()+[0]] # first adddress is the op of the root of T
    left_al = op_address_list(T[1], prefix.copy()+[1])
    L.extend(left_al)
    right_al = op_address_list(T[2], prefix.copy()+[2])
    L.extend(right_al)
    
    return L


def num_address_list(T, prefix = None):
    '''
    Return the address list L + R of the internal nodes of the expresssion tree T
    
    If T is a scalar, then L + R = [] 

    Note that the function 'decompose' is more general.

    Parameters
    ----------
    T : expression tree
    prefix: prefix to prepend to the addresses returned in L + R

    Returns
    -------
    L + R
    '''
    if isinstance(T, int):
        return []

    if prefix is None:
        prefix = []

    L = [prefix.copy()+[1]] if isinstance(T[1], int) else []
    left_al = num_address_list(T[1], prefix.copy()+[1])
    L.extend(left_al)

    R = [prefix.copy()+[2]] if isinstance(T[2], int) else []
    right_al = num_address_list(T[2], prefix.copy()+[2])
    R.extend(right_al)

    return L + R


# ----------------------------------------------------------------------------

def decompose(T, prefix = None):
    '''
    Compute
        Aop : address list of the operators
        Lop : list of the operators
        Anum : address of the numbers
        Lnum : list of the numbers
    
    For example, if 
        T =  ['-', ['+', ['-', 75, ['-', 10, 3]], ['-', 100, 50]], 3]
    
        Aop is  [[0], [1, 0], [1, 1, 0], [1, 1, 2, 0], [1, 2, 0]] 
        Lop is  ['-', '+', '-', '-', '-'] 
        Anum is [[1, 1, 1], [1, 1, 2, 1], [1, 1, 2, 2], [1, 2, 1], [1, 2, 2], [2]] 
        Lnum is [75, 10, 3, 100, 50, 3]    
    
    Parameters
    ----------
    T : expression tree 
    
    prefix : address to preprend 

    Returns
    -------
    Aop, Lop, Anum, Lnum

    '''
    Aop = []
    Lop = []
    Anum = []
    Lnum = []

    # If T is scalar set some default values
    if isinstance(T, int):
        Anum = [prefix]
        Lnum = [T]
    else:
        if prefix is None:
            prefix = []

        for i, v in enumerate(T):
            # Create a copy of the path we have incase previous paths have alternate routes
            # e.g. a previous right child was also a subtree
            p = prefix + [i]

            # Check tree children
            if v in OPERATORS:
                Aop.append(p)
                Lop.append(v)
            elif isinstance(v, int):
                Anum.append(p)
                Lnum.append(v)               
            elif isinstance(v, list):
                aop, lop, anum, lnum = decompose(v, p)
                Aop.extend(aop)
                Lop.extend(lop)
                Anum.extend(anum)
                Lnum.extend(lnum)

    return Aop, Lop, Anum, Lnum   
    
# ----------------------------------------------------------------------------

def get_item(T, a):
    '''
    Get the item at address a in the expression tree T

    Parameters
    ----------
    T : expression tree
    a : valid address of an item in the tree

    Returns
    -------
    the item at address a

    '''
    if len(a)==0:
        return T
    # else
    return get_item(T[a[0]], a[1:])

# ----------------------------------------------------------------------------

def replace_subtree(T, a, S):
    '''
    Replace the subtree at address a
    with the subtree S in the expression tree T
    
    The address a is a sequence of integers in {0,1,2}.
    
    If a == [] , then we return S
    If a == [1], we replace the left subtree of T with S
    If a == [2], we replace the right subtree of T with S

    Returns
    ------- 
    The modified tree

    Warning: the original tree T is modified. 
             Use copy.deepcopy()  if you want to preserve the original tree.
    '''    
    
    # base case, address empty
    if (a == None):
        return S
    if len(a)==0:
        return S
    
    # recursive case
    T[a[0]] = replace_subtree(T[a[0]], a[1:], S)
    return T

# ----------------------------------------------------------------------------

def mutate_num(T, Q):
    '''
    Mutate one of the numbers of the expression tree T
    
    Parameters
    ----------
    T : expression tree
    Q : list of numbers initially available in the game
    Returns
    -------
    A mutated copy of T
    '''

    if isinstance(T, int):
        return T

    _, _, Anum, Lnum = decompose(T)

    if len(Q) == len(Lnum):
        return T

    # Discover possible mutations, removing used large numbers
    Q_count = collections.Counter(Q)
    L_count = collections.Counter(Lnum)
    mut_Q = list((Q_count - L_count).elements())

    # Setup values
    mut_T = copy.deepcopy(T)
    mut_A = random.choice(Anum)
    mut_S = random.choice(mut_Q)
    
    # Begin and return mutated tree
    return replace_subtree(mut_T, mut_A, mut_S)

# ----------------------------------------------------------------------------

def mutate_op(T):
    '''
    Mutate an operator of the expression tree T
    If T is a scalar, return T
    Parameters
    ----------
    T : non trivial expression tree
    Returns
    -------
    A mutated copy of T
    '''
    if isinstance(T, int):
        return T

    Aop = op_address_list(T)
    
    mut_T = copy.deepcopy(T)
    mut_A = random.choice(Aop)
    used_op = get_item(mut_T, mut_A)
    mut_Q = set(OPERATORS) - set(used_op)
    mut_S = random.choice(list(mut_Q))
    
    # Begin and return mutated tree
    return replace_subtree(mut_T, mut_A, mut_S)
    

# ----------------------------------------------------------------------------

def cross_over(P1, P2, Q):    
    '''
    Perform crossover on two non trivial parents
    
    Parameters
    ----------
    P1 : parent 1, non trivial expression tree  (root is an op)
    P2 : parent 2, non trivial expression tree  (root is an op)
        DESCRIPTION
        
    Q : list of the available numbers
        Q may contain repeated small numbers    
        

    Returns
    -------
    C1, C2 : two children obtained by crossover
    '''
    
    def get_num_ind(aop, Anum):
        '''
        Return the indices [a,b) of the range of numbers
        in Anum and Lum that are in the sub-tree 
        rooted at address aop

        Parameters
        ----------
        aop : address of an operator (considered as the root of a subtree).
              The address aop is an element of Aop
        Anum : the list of addresses of the numbers

        Returns
        -------
        a, b : endpoints of the semi-open interval
        
        '''
        d = len(aop)-1  # depth of the operator. 
                        # Root of the expression tree is a depth 0
        # K: list of the indices of the numbers in the subtrees
        # These numbers must have the same address prefix as aop
        p = aop[:d] # prefix common to the elements of the subtrees
        K = [k for k in range(len(Anum)) if Anum[k][:d]==p ]
        return K[0], K[-1]+1
        # .........................................................
        
    Aop_1, Lop_1, Anum_1, Lnum_1 = decompose(P1)
    Aop_2, Lop_2, Anum_2, Lnum_2 = decompose(P2)

    C1 = copy.deepcopy(P1)
    C2 = copy.deepcopy(P2)
    
    i1 = np.random.randint(0,len(Lop_1)) # pick a subtree in C1 by selecting the index
                                         # of an op
    i2 = np.random.randint(0,len(Lop_2)) # Select a subtree in C2 in a similar way
 
    # i1, i2 = 4, 0 # DEBUG    
 
    # Try to swap in C1 and C2 the sub-trees S1 and S2 
    # at addresses Lop_1[i1] and Lop_2[i2].
    # That's our crossover operation!
    
    # Compute some auxiliary number lists
    
    # Endpoints of the intervals of the subtrees
    a1, b1 = get_num_ind(Aop_1[i1], Anum_1)     # indices of the numbers in S1 
                                                # wrt C1 number list Lnum_1
    a2, b2 = get_num_ind(Aop_2[i2], Anum_2)   # same for S2 wrt C2
    
    # Lnum_1[a1:b1] is the list of numbers in S1
    # Lnum_2[a2:b2] is the list of numbers in S2
    
    # numbers is C1 not used in S1
    nums_C1mS1 = Lnum_1[:a1]+Lnum_1[b1:]
    # numbers is C2-S2
    nums_C2mS2 = Lnum_2[:a2]+Lnum_2[b2:]
    
    # S2 is a fine replacement of S1 in C1
    # if nums_S2 + nums_C1mS1 is contained in Q
    # if not we can bottom up a subtree with  Q-nums_C1mS1

    counter_Q = collections.Counter(Q) # some small numbers can be repeated
    
    d1 = len(Aop_1[i1])-1
    aS1 = Aop_1[i1][:d1] # address of the subtree S1 
    S1 = get_item(C1, aS1)

    d2 = len(Aop_2[i2])-1
    aS2 = Aop_2[i2][:d2] # address of the subtree S2 
    S2 = get_item(C2, aS2)

    # print(' DEBUG -------- S1 and S2 ----------') # DEBUG
    # print(S1)
    # print(S2)

    # count the numbers (their occurences) in the candidate child C1
    counter_1 = collections.Counter(Lnum_2[a2:b2]+nums_C1mS1)
    
    # Test whether child C1 is ok
    if all(counter_Q[v]>=counter_1[v]  for v in counter_Q):
        # candidate is fine!  :-)
        C1 = replace_subtree(C1, aS1, S2)
    else:
        available_nums = counter_Q.copy()
        available_nums.subtract(
            collections.Counter(nums_C1mS1)
            )
        R1, _ = bottom_up_creator(list(available_nums.elements()))
        C1 = replace_subtree(C1, aS1, R1)
        
    # count the numbers (their occurences) in the candidate child C2
    counter_2 = collections.Counter(Lnum_1[a1:b1]+nums_C2mS2)
    
    # Test whether child C2 is ok
    if all(counter_Q[v]>=counter_2[v]  for v in counter_Q):
        # candidate is fine!  :-)
        C2 = replace_subtree(C2, aS2, S1)
    else:
        available_nums = counter_Q.copy()
        available_nums.subtract(
            collections.Counter(nums_C2mS2)
            )
        R2, _ = bottom_up_creator(list(available_nums.elements()))
        C2 = replace_subtree(C2, aS2, R2)    
    
    return C1, C2

default_GA_params = {
    'max_num_iteration': 50,
    'population_size':100,
    'mutation_probability':0.1,
    'elit_ratio': 0.05,
    'parents_portion': 0.3,
    'break_on_success': True
}

def evolve_pop(Q, target, **ga_params):
    '''
    
    Evolve a population of expression trees for the game
    Letters and Numbers given a target value and a set of numbers.
    

    Parameters
    ----------
    Q : list of integers
        Integers that were drawn by the game host
    
    target: integer
           target value of the game
        
    params : dictionary, optional
        The default is GA_params.
        Dictionary of parameters for the genetic algorithm

    Returns
    -------
    v, T: the best expression tree found and its value

    '''
    
    params = default_GA_params.copy()
    params.update(ga_params)
    
    mutation_probability = params['mutation_probability']
    pop_size = params['population_size']
    
    # ------------- Initialize Population ------------------------
    
    pop = [] # list of pairs (cost, individuals)
    
    for _ in range(pop_size):
        T, _ = bottom_up_creator(Q)
        cost = abs(target-eval_tree(T))
        pop.append((cost,T))
    
    # Sort the initial population
    # print(pop) # debug
    pop.sort(key=lambda x:x[0])

    # ------------- Loop on generations ------------------------
    
    # Rank of last individual in the current population
    # allowed to breed.
    rank_parent = int(params['parents_portion'] * 
                                      params['population_size'])
    
    # Rank of the last elite individual. The elite is copied unchanged 
    # into the next generation.
    rank_elite = max(1, int(params['elit_ratio'] *
                                      params['population_size']))
 
    for g in range(params['max_num_iteration']):
        
        # Generate children
        children = []
        while len(children) < pop_size:
            # pick two parents
            (_, P1), (_, P2) = random.sample(pop[:rank_parent], 2)
            # skip cases where one of the parents is trivial (a number)
            if isinstance(P1, list) and isinstance(P2, list):
                C1, C2 = cross_over(P1, P2, Q)
            else:
                # if one of the parents is trivial, just compute mutants
                C1 = mutate_num(P1,Q)
                C2 = mutate_num(P2,Q)
            # Compute the costs of the children
            cost_1 =  abs(target-eval_tree(C1))
            cost_2 =  abs(target-eval_tree(C2))
            children.extend([ (cost_1,C1), (cost_2,C2) ])
             
        new_pop = pop[rank_elite:]+children 
        
        # Mutate some individuals (keep aside the elite for now)
        # Pick randomly the indices of the mutants
        mutant_indices = random.sample(range(len(new_pop)), 
                                       int(mutation_probability*pop_size))      
        # i: index of a mutant in new_pop
        for i in mutant_indices:
            # Choose a mutation by flipping a coin
            Ti = new_pop[i][1]  #  new_pop[i][0]  is the cost of Ti
            # Flip a coin to decide whether to mutate an op or a number
            # If Ti is trivial, we can only use mutate_num
            if isinstance(Ti, int) or random.choice((False, True)): 
                Mi = mutate_num(Ti, Q)
            else:
                Mi = mutate_op(Ti)
            # update the mutated entry
            new_pop[i] = (abs(target-eval_tree(Mi)), Mi)
                
        # add without any chance of mutation the elite
        new_pop.extend(pop[:rank_elite])
        
        # sort
        new_pop.sort(key=lambda x:x[0])
        
        # keep only pop_size individuals
        pop = new_pop[:pop_size]
        
        if pop[0][0] == 0:
            # found a solution!
            break

      # return best found
    return pop[0]

def evolve_pop_limit_2seconds(Q, target, **ga_params):
    '''
    
    Evolve a population of expression trees for the game
    Letters and Numbers given a target value and a set of numbers.
    Terminating after a duration of 2 seconds.
    

    Parameters
    ----------
    Q : list of integers
        Integers that were drawn by the game host
    
    target: integer
           target value of the game
        
    params : dictionary, optional
        The default is GA_params.
        Dictionary of parameters for the genetic algorithm

    Returns
    -------
    v, T: the best expression tree found and its value

    '''
    
    params = default_GA_params.copy()
    params.update(ga_params)
    
    mutation_probability = params['mutation_probability']
    pop_size = params['population_size']
    
    # ------------- Initialize Population ------------------------
    
    pop = [] # list of pairs (cost, individuals)
    
    for _ in range(pop_size):
        T, _ = bottom_up_creator(Q)
        cost = abs(target-eval_tree(T))
        pop.append((cost,T))
    
    # Sort the initial population
    pop.sort(key=lambda x:x[0])

    # ------------- Loop on generations ------------------------
    
    # Rank of last individual in the current population
    # allowed to breed.
    rank_parent = int(params['parents_portion'] * 
                                      params['population_size'])
    
    # Rank of the last elite individual. The elite is copied unchanged 
    # into the next generation.
    rank_elite = max(1, int(params['elit_ratio'] *
                                      params['population_size']))

    break_on_success = params['break_on_success']

    g = 0
    t_start = time.time()
    t_end = t_start + 2
    while (time.time() < t_end):     
           
        # Generate children
        children = []
        while len(children) < pop_size and time.time() < t_end:
            # pick two parents
            (_, P1), (_, P2) = random.sample(pop[:rank_parent], 2)
            # skip cases where one of the parents is trivial (a number)
            if isinstance(P1, list) and isinstance(P2, list):
                C1, C2 = cross_over(P1, P2, Q)
            else:
                # if one of the parents is trivial, just compute mutants
                C1 = mutate_num(P1,Q)
                C2 = mutate_num(P2,Q)
            # Compute the costs of the children
            cost_1 =  abs(target-eval_tree(C1))
            cost_2 =  abs(target-eval_tree(C2))
            children.extend([ (cost_1,C1), (cost_2,C2) ])
             
        new_pop = pop[rank_elite:]+children 
        
        # Mutate some individuals (keep aside the elite for now)
        # Pick randomly the indices of the mutants
        mutant_indices = random.sample(range(len(new_pop)), 
                                       int(mutation_probability*pop_size))      
        # i: index of a mutant in new_pop
        for i in mutant_indices:

            if time.time() >= t_end:
                break

            # Choose a mutation by flipping a coin
            Ti = new_pop[i][1]  #  new_pop[i][0]  is the cost of Ti
            # Flip a coin to decide whether to mutate an op or a number
            # If Ti is trivial, we can only use mutate_num
            if isinstance(Ti, int) or random.choice((False, True)): 
                Mi = mutate_num(Ti, Q)
            else:
                Mi = mutate_op(Ti)
            # update the mutated entry
            new_pop[i] = (abs(target-eval_tree(Mi)), Mi)
                
        # Calculate end time here, sorting stuff below isnt part of the algorithm
        t_taken = time.time() - t_start

        # Add without any chance of mutation the elite
        new_pop.extend(pop[:rank_elite])
        
        # Sort by cost
        new_pop.sort(key=lambda x:x[0])
        
        # keep only pop_size individuals
        pop = new_pop[:pop_size]
        
        # If a correct value has been found
        if pop[0][0] == 0 and break_on_success:
            # found a solution!
            break
        
        # Above loops could terminate before time is over, thus the generation failed. 
        # check again before we increase the generation counter.
        if time.time() < t_end:
            g += 1

      # return best found
    return list(pop[0]) + [t_taken, g]

# ----------------------------------------------------------------------------

def find_max_gen_pairs(Q, target, max_population):
    '''
    
    Returns a list of population / generation pairs generated over a 
    budget of 2 seconds per evolution. Appends both successful and 
    unsuccessful results.
    

    Parameters
    ----------
    Q : list of integers
        Integers that were drawn by the game host
    
    target: integer
           target value of the game

    max_population: integer
        Maximum population to step towards

    Returns
    -------
    pairs : the list of tuple pairs

    '''
    pairs = []

    # Enumerate an appropriate range of population values along a logarithmic scale
    for i, pop in enumerate(np.concatenate([[x for x in np.geomspace(a, b, num=n, dtype=int)] for n, a, b in [ (2, 15,50), (16, 100, 950), (2, 1000, 1500)]])):
        _, _, _, gen = evolve_pop_limit_2seconds(Q, target, population_size=pop, parents_portion=0.3, break_on_success=False)

        pairs.append((pop, gen))
        print(f"[{i+1:>2}] Population of [{pop:>5}] evolved for [{gen:>4}] generations.")
            
    if len(pairs) == 0:
        print("Terminated before finding any pairs. Trying again.")
        return find_max_gen_pairs(Q, target, max_population)

    print(f"{'-'*75}\n")
    
    # Return results
    return pairs

def find_best_combinations(Q, target, max_population):
    '''
    
    Returns the best possible population and iteration inputs to the 
    genetic algorithm for a specific Q and target. Result returned is 
    based on highest success rate and shortest time taken to succeed.
    

    Parameters
    ----------
    Q : list of integers
        Integers that were drawn by the game host
    
    target: integer
           target value of the game

    Returns
    -------
    p : integer
        Best population_size result
    g : integer
        Best max_num_iteration result

    '''

    # Find the best pairs over 2 seconds
    print(f"\nFind pop, max_num_iterations pairs given budget of (2) seconds:\n{'='*75}\n max_population = {max_population}\n{'-'*75}")
    pairs = find_max_gen_pairs(Q, target, max_population)
    
    # Debug Values:
    # Q = [7, 5, 8, 75, 4, 7]
    # target = 147
    # pairs = [(15, 2084), (1289, 20), (2564, 10), (3839, 7), (5114, 4), (6389, 4), (7664, 3), (8939, 2), (10214, 2), (11489, 2), (12763, 1), (14038, 1), (15313, 1), (16588, 1), (17863, 1), (19138, 1), (20413, 1), (21688, 1), (22963, 1), (24238, 1)]

    # Find the best possible combination
    print(f"\nFind Best Combination given:\n{'='*75}\n Pairs = {pairs}\n{'-'*75}")
    num_tests = 30
    results = []

    for i, (pop, gen) in enumerate(pairs):
        successes = 0
        t_start = time.time()
        for _ in range(num_tests):
            cost, _ = evolve_pop(Q, target, population_size=pop, max_num_iteration=gen, parents_portion=0.3)

            # If value found, increase number of successes
            if (cost == 0):
                successes += 1
        
        t_end = time.time() - t_start # time taken

        # Append result
        results.append([successes, t_end, pop, gen])

        # Debug: Print pair result
        print(f"[{i+1:>2}] Population of [{pop:>5}] evolved for [{gen:>4}] generations. Passed [{successes:>2}/{num_tests:<2}] tests over {t_end:.4f} seconds.")

    # Sort results by descending successes and shortest time taken
    results.sort(key=lambda x: (-x[0], x[1]) )

    # Unpack fastest result
    successes, _, pop_size, max_gen = results[0]

    # Debug: Print optimal result
    print(f"{'-'*75}\nFor:\n Q = {Q}\n target = {target}\nThe best combination is:\n population_size = {pop_size}\n max_num_iteration = {max_gen}\n with a success rate of {(successes/num_tests)*100:.2f}%\n{'-'*75}")

    # Return best combination
    return pop_size, max_gen

if __name__ == '__main__':
    # T = polish_str_2_expr_tree("['-', ['+', ['-', 75, ['-', 10, 3]], ['-', 100, 50]], 3]")

    # print(eval_tree(T))

    # Aop, Lop, Anum, Lnum = decompose(T)
    # print(Aop,"|", Lop)
    # print(Anum,"|",Lnum)

    Q = [7, 5, 8, 75, 4, 7]
    target = 147

    population_size, max_num_iteration = find_best_combinations(Q, target, 2000)
    


# print(polish_str_2_expr_tree("10000005535"))
# print(polish_str_2_expr_tree("(5*4)+100"))
# listvar = polish_str_2_expr_tree("((5*4)+100)*(10-1)")
# print("------------------------------------------------------")
# print(listvar)
# Aop, Lop, Anum, Lnum = decompose(["*",["-",4,3],["-",4,["-",4,3]]])#["*",["+",5,4],["-"["+",2,1],5]])
# print("_____________________________________________________")
# print(Aop,"|", Lop)
# print(Anum,"|",Lnum)
