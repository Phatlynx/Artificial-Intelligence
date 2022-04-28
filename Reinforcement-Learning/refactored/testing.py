import time
from wsgiref.util import setup_testing_defaults
from q_learning2 import *


def makeExp(expNum, subExp=None, seed=None):
    tic = time.process_time() # https://www.tutorialspoint.com/python/time_clock.htm
    sarsa = True if expNum == 2 else False

    exp = experiment(expNum, subExp, SARSA=sarsa, seed=seed)
    toc = time.process_time()
    print(f"This took {toc-tic}s")
    #exp.print_qTable()
    print(f"Terminal States reached: {exp.terminalStatesReached}")
    print(f"Steps per terminal state:{exp.stepsPerTerminalState}")
    print(f"Sanity Check: 8000 >=? {sum(exp.stepsPerTerminalState)}")
    #print(f"Female rewards: {exp.FReward}")
    #print(f"Male rewards: {exp.MReward}")
    print("ending board:", "\n", exp.tokensOnBoard)
    print("\n\n")
    with open("refactored/movements.txt",'w') as f:
        maleMovements = [i[1] for i in exp.maleStateActionRewardHistroy]
        femaMovements = [i[1] for i in exp.femaStateActionRewardHistory]
        movements = list(zip(femaMovements, maleMovements))
        counter = 0
        for i in movements:
            counter2 = counter+1 
            f.write(f"step {counter}: {i[0]}\t\tstep {counter2}: {i[1]}\n")
            counter += 2
    return exp

# exp1a = makeExp(1, 'a', seed=1)
# exp1b = makeExp(1, 'b', seed=1)
# exp1c = makeExp(1,'c', seed=1)

# aAL = exp1a.getActionList()
# bAL = exp1b.getActionList()
# print(f"len(aAL)=={len(aAL)}, len(bAL)=={len(bAL)}")
# for i,_ in enumerate(aAL):
#     if aAL[i] != bAL[i]:
#         print(f"step {i}")
#         break


seed=1
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
