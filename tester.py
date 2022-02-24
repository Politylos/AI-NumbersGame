#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Apr  8 17:56:28 2021

@author: frederic


Test crossover



"""

# from lan import mutate, get_item, op_address_list, decompose
from number_game import *



Q = pick_numbers()
# target = np.random.randint(1,1000)


# Q = [100, 50, 3, 3, 10, 75]
# Q.sort()

target = 322

# 


while True:
    Q = pick_numbers()
    P1, U1 = bottom_up_creator(Q)
    P2, U2 = bottom_up_creator(Q)
    if isinstance(P1, list) and isinstance(P2, list):
        break
    else:
        print('try again')

# Q = [9, 3, 6, 8, 5, 10]
# P1 = ['+', 3, ['-', ['+', 6, ['+', 9, 5]], ['+', 8, 10]]]
# P2 = ['-', 3, ['-', 6, 9]]

 
print('------------- Q ----------')
print(Q)
print('-------------- parents -------- ')
print(P1)

print(P2)

C1, C2 = cross_over(P1, P2, Q)

print('-------------- children -------- ')

    
print(C1)
print(C2)

print('-------------- display child 1 -------- ')

display_tree(C1)

