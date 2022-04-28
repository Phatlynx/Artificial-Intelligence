#!/usr/bin/env python3

import time
from q_learning import *

def makeExp(expNum, subExp=None, seed=None):
    tic = time.process_time() # https://www.tutorialspoint.com/python/time_clock.htm
    sarsa = True if expNum == 2 else False

    exp = experiment(expNum, subExp, SARSA=sarsa, seed=seed)
    toc = time.process_time()
    print(f"took {toc-tic}s")
    print(f"Terminal States reached: {exp.terminalStatesReached}")
    print(f"Steps   per terminal state: {exp.stepsPerTerminalState}")
    print(f"Rewards per terminal state: {exp.totalRewardsPerEpisode}")
    exp.output_qTable(f"experiment_{expNum}_{subExp}_seed_{seed}_final_qTable.txt")
    # visualize_get_actionList(exp)
    print("\n\n")

def visualize_get_actionList(exp):
    exp.visualize_steps_per_terminal_state()
    exp.visualize_rewards_per_terminal_state()
    return exp.getActionList()

# this codeblock runs all experiments for hivemind == True
# hive = True is for single Q-table and hive = False is for individual Q-table
hive = True
seeds=[577, 440] if hive else [326, 123]
for seed in seeds:
    for expNum in [1,2,3,4]:
        sarsa = True if expNum == 2 else False
        if expNum == 1:
            for subExp in ['a','b','c']:
                makeExp(expNum, subExp, seed=seed)
        elif expNum == 3:
            for subExp in ['a','b']:
                makeExp(expNum, subExp, seed=seed)
        elif expNum == 2:
            makeExp(expNum, seed=seed)
        else:#expNum == 4
            exp = makeExp(expNum, seed=seed)




# # if you want to run just a single experiment uncomment lines 46-65 and make changes to hive, seed, expNum, and subExp
# hive = True
# #if hive == True:
# seeds=577 #or 440
# #else if hive == False:
# #seed == 326 #or 123
# expNum = 1 # or 2, 3, 4
# subExp = 'a' # or 'b', 'c', or None

# sarsa = True if expNum == 2 else False
# if expNum == 1:
#     for subExp in ['a','b','c']:
#         makeExp(expNum, subExp, seed=seed)
# elif expNum == 3:
#     for subExp in ['a','b']:
#         makeExp(expNum, subExp, seed=seed)
# elif expNum == 2:
#     makeExp(expNum, seed=seed)
# else:#expNum == 4
#     exp = makeExp(expNum, seed=seed)
