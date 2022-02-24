#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Apr 17 17:46:18 2021

@author: frederic

***** Perfect Score!! *****
    Q = [25,10,2,9,8,7]
    target 449 , tree value 449
    
    -
    |+
    ||*
    |||*
    ||||2
    |||
    ||||9
    ||
    |||25
    |
    ||7
    
    |8
    
**** Perfect Score!! *****
    Q = [50,75,9,10,2,2]
    target 533 , tree value 533
    
    +
    |+
    ||75
    |
    ||-
    |||*
    ||||9
    |||
    ||||50
    ||
    |||2
    
    |10

"""

import numpy as np

from number_game import pick_numbers, eval_tree, display_tree

from genetic_algorithm import  evolve_pop


Q = pick_numbers()
target = np.random.randint(1,1000)


# Q = [100, 50, 3, 3, 10, 75]
# target = 322

# Q = [25,10,2,9,8,7]
# target = 449

# Q = [50,75,9,10,2,2]
# target = 533

Q = [100,25,7,5,3,1]
target = 728

Q.sort()

print('List of drawn numbers is ',Q)

v, T = evolve_pop(Q, target, 
                  max_num_iteration = 200,
                  population_size = 500,
                  parents_portion = 0.3)



print('----------------------------')
if v==0:
    print("\n***** Perfect Score!! *****")
print(f'\ntarget {target} , tree value {eval_tree(T)}\n')
display_tree(T)

