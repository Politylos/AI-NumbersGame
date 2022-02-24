#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""

Module defining a function for evolving a population with a basic GA.


Created on Fri Apr 16 21:48:00 2021

@author: frederic

algorithm_parameters={'max_num_iteration': None,\
                                       'population_size':100,\
                                       'mutation_probability':0.1,\
                                       'elit_ratio': 0.01,\
                                       'crossover_probability': 0.5,\
                                       'parents_portion': 0.3,\
                                       'crossover_type':'uniform',\
                                       'max_iteration_without_improv':None},\

"""

from number_game import (bottom_up_creator, eval_tree, cross_over, 
                         mutate_num, mutate_op, display_tree)


# import copy
import random

default_GA_params = {
    'max_num_iteration': 50,
    'population_size':100,
    'mutation_probability':0.1,
    'elit_ratio': 0.05,
    'parents_portion': 0.3}


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
    
    print('GA Parameters ', params)
    
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
    
    # Report
    print('\n'+'-'*40+'\n')
    print("The best individual of the initial population has a cost of {}".format(pop[0][0]))
    print("The best individual is \n")
    display_tree(pop[0][1])
    print('\n')
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
        
        # Report some stats
        print(f"\nAfter {g+1} generations, the best individual has a cost of {pop[0][0]}\n")
        
        if pop[0][0] == 0:
            # found a solution!
            break

      # return best found
    return pop[0]
