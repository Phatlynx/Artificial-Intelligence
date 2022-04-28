from itertools import count
import random
from tracemalloc import start
import numpy as np
import seaborn as sb
import matplotlib.pyplot as plt
from copy import deepcopy
import os

class experiment:
    def __init__(self, experiment, subExperiment=None, SARSA=False, seed=None):
        random.seed(seed)  # for reproducibility
        np.random.seed(seed)
        self.filestream = open("refactored/allSteps.txt", "w")
        self.experimentName = f"Experiment {str(experiment)}"
        if subExperiment != None:
            self.experimentName += f"{subExperiment}"
        self.tokensOnBoard = np.array([
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ])  # the elements of the board represent resource tokens at that position
        self.dropOffCells = [(0, 0), (0, 4), (2, 2), (4, 4)]
        self.dropOffCellCapacity = 5
        self.pickUpCells = [(2, 4), (3, 1)]
        self.stepCounter = 0
        self.pickUpCellsStartWith = 10
        # next two bool variables represent whether the specified player is holding a token
        self.maleHolding = False
        self.femaHolding = False

        self.malePos = np.array([4, 2])  # initial location of male agent
        self.femaPos = np.array([0, 2])  # initial location of fema agent

        self.currentState = (0,2,0,4,2,0,0,0,0,0,0,0) #car,cac,cah,oar,oac,oah,PU1es,PU2es,DO1fs,DO2fs,DO3fs,DO4fs
        

        self.maleRewards = []  # rewards for male for each stage
        self.femaRewards = []  # rewards for fema for each stage

        self.MReward = []  # stores total rewards for male to reach each terminal stage
        self.FReward = []  # stores total rewards for fema to reach each terminal stage

        # these next two are list of lists where each inner list is a nupy array representing position, a string representing the movement-action taken in that position, and the reward for that movement - just had to change the nextPosition function to implement updates
        # these are used for SARSA
        self.maleStateActionRewardHistroy = []
        self.femaStateActionRewardHistory = []
        # if it turns out our qTable needs to have actions for pickUp and dropOff then these lists need to shift to represent all actions (not just movement actions) and the pickUp and dropOff functiosn will have to be changed

        self.directionOffset = {"north": np.array([-1, 0]), "south": np.array([1, 0]), "east": np.array([0, 1]),"west": np.array([0, -1])}

        self.learning_rate = None
        self.discount_factor = None
        self.SARSA = None
        self.terminalStatesReached = 0
        self.stepsPerTerminalState = []
        self.actionList = []

        # Q Table
        FT = [False, True]
        cAgentHoldingStatuses = FT # current agent holding statuses
        oAgentHoldingStatuses = FT # other agent holding statuses
        pickUpExhaustedStatuses = FT
        dropOffFullStatuses = FT
        states = [(car,cac,cah,oar,oac,oah,PU1es,PU2es,DO1fs,DO2fs,DO3fs,DO4fs)
        for car in range(5) for cac in range(5) for cah in cAgentHoldingStatuses 
        for oar in range(5) for oac in range(5) for oah in oAgentHoldingStatuses 
        for PU1es in pickUpExhaustedStatuses for PU2es in pickUpExhaustedStatuses 
        for DO1fs in dropOffFullStatuses for DO2fs in dropOffFullStatuses for DO3fs in dropOffFullStatuses for DO4fs in dropOffFullStatuses]
        actions = ["north", "south", "west", "east", "pickUp", "dropOff"]
        #now we make our qTable from our states and actions
        self.qTable = {state:{action:0 for action in actions} for state in states} # Q TABLE Q TABLE Q TABLE Q TABLE Q TABLE Q TABLE Q TABLE Q TABLE Q TABLE  


        self.resetWorld()
        self.SARSA = SARSA
        if experiment == 1 or experiment == 2 or experiment == 4:
            self.learning_rate = 0.3
            self.discount_factor = 0.5
            if experiment == 1:
                self.experiment1(subExperiment)
            elif experiment == 2:
                self.experiment2()
            elif experiment == 4:
                self.experiment4()
        elif experiment == 3:
            if subExperiment == 'c':
                return
            elif subExperiment == 'a':
                self.learning_rate = 0.15
                self.discount_factor = 0.5
            elif subExperiment == 'b':
                self.learning_rate = 0.45
                self.discount_factor = 0.5
            self.experiment3()

        self.filestream.close()
        with open('refactored/qTable.txt', 'w') as f:
            for state in self.qTable:
                f.write(f"{str(state)}\t\t{str(self.qTable[state])}\n")

    def POLICY(self, step: int, policy: str):
        def getReward(action):
            return 13 if action == "pickUp" or action == "dropOff" else -1
        
        def getApplicableActions(state): # state = [car,cac,cah,oar,oac,oah,PU1es,PU2es,DO1fs,DO2fs,DO3fs,DO4fs]
            car,cac,cah,oar,oac,_,_,_,_,_,_,_ = state
            applicableActions = []
            if car > 0 and car-1 != oar:# if the agent is not blocked north then add north
                applicableActions.append("north") # +[-1,0]
            if car < 4 and car+1 != oar:# if the agent is not blocked south then add south
                applicableActions.append("south") # +[1,0]
            if cac > 0 and cac+1 != oac:# if the agent is not blocked west then add west
                applicableActions.append("west") # +[0,-1]
            if cac < 4 and cac-1 != oac:# if the agent is not blocked east then add east
                applicableActions.append("east") # +[0,1]
            if cah == False and (car,cac) in self.pickUpCells and self.tokensOnBoard[car,cac] > 0:
                applicableActions.append("pickUp")
            if cah == True and (car,cac) in self.dropOffCells and self.tokensOnBoard[car,cac] < 5:
                applicableActions.append("dropOff")
            return applicableActions
        
        def getExhaustedFullStatuses():
           PUExhaustedStatuses = [self.tokensOnBoard[PUcell]==0 for PUcell in self.pickUpCells]
           DOFullStatuses = [self.tokensOnBoard[DOcell]<5 for DOcell in self.dropOffCells]
           return *PUExhaustedStatuses,*DOFullStatuses

        def updateQtable(step, startState, action):
            if step >= 2 and self.SARSA: # SARSA
                oldState, oldAction, _ = self.maleStateActionRewardHistory[-2] if step%2 else self.femaStateActionRewardHistory[-2]
                self.qTable[oldState][oldAction] += self.learning_rate * \
                    (getReward(oldAction) \
                        + self.discount_factor * self.qTable[startState][action] \
                            - self.qTable[oldState][oldAction])
            else: # Q-update
                self.qTable[startState][action] += self.learning_rate * \
                    (getReward(action) \
                        + self.discount_factor * max([self.qTable[self.currentState][action] for action in getApplicableActions(self.currentState)]) \
                            - self.qTable[startState][action])
                #print(f"step {step}: {startState}, {action}: {self.qTable[startState][action]}") ###########################################################################################
    
        def terminalState():  # re-wrote this so that it's more flexible (for when we change drop-off and pick-up locations)
            dropOffsFull = [self.tokensOnBoard[pos] == 5 for pos in self.dropOffCells]
            return all(dropOffsFull)

        if terminalState():
            self.terminalStatesReached += 1
            self.MReward.append(sum(self.maleRewards))  # adding sum of male reward from current terminal state
            self.maleRewards = []  # initializing male reward to 0
            self.FReward.append(sum(self.femaRewards))  # adding sum of fema reward from current terminal state
            self.femaRewards = []  # initializing fema reward to 0
            self.stepsPerTerminalState.append(self.stepCounter)
            self.stepCounter = 0
            self.resetWorld()
        
        startState = deepcopy(self.currentState) # need the deepcopy bc we want two separate items in memory
        #print(startState)
        startPos = startState[:2]
        startHolding = startState[2]
        applicableActions = getApplicableActions(startState)

        if not startHolding and startPos in self.pickUpCells and self.tokensOnBoard[startPos] > 0:  # if we can pick up then do so
            action = "pickUp"
            self.tokensOnBoard[startPos] -= 1
            # update current state's current agent's holding status
            newCurrentState = list(self.currentState)
            newCurrentState[6:] = getExhaustedFullStatuses()
            newCurrentState[2] = True
            self.currentState = tuple(newCurrentState) 
        elif startPos in self.dropOffCells and self.tokensOnBoard[startPos] < 5 and startHolding:  # else if we can drop off then do so:  # else if we can drop off then do so
            action = "dropOff"
            self.tokensOnBoard[startPos] += 1
            # update current state's current agent's holding status
            newCurrentState = list(self.currentState)
            newCurrentState[6:] = getExhaustedFullStatuses()
            newCurrentState[2] = False
            self.currentState = tuple(newCurrentState)
        else:  # else make a move
            # decide which move to make based on policy
            if policy == "PRANDOM":
                ri = np.random.randint(0,len(applicableActions))
                action = applicableActions[ri] # get random applicable action
            elif policy == "PGREEDY":
                action = max([[action, self.qTable[startState][action]] for action in applicableActions], key = lambda x:x[1])[0] # get action with highest q value that is applicable
            elif policy == "PEXPLOIT":
                decideWhich = np.random.uniform()
                if decideWhich < 0.8:
                    action = max([[action, self.qTable[startState][action]] for action in applicableActions], key = lambda x:x[1])[0] # get action with highest q value that is applicable
                else:
                    action = applicableActions[np.random.randint(0,len(applicableActions))] # get random applicable action
            else:
                print("Incorrect specification of policy name. Should be 'PRANDOM', 'PGREEDY', or 'PEXPLOIT'")
                exit()
            # make the move
            self.currentState = tuple(list(np.array(self.currentState[:2]) + self.directionOffset[action]) + list(self.currentState[2:]))

        #output for debugging
        if step%2:
            mR,mC,mH,fR,fC,fH, _,_,_,_,_,_ = startState
        else:
            fR,fC,fH,mR,mC,mH, _,_,_,_,_,_ = startState

        if action == ("pickUp" or "dropOff"):
            #print(f"step {step}:\n\t{'*' if mH else ' '}{mR,mC}{'t' if step%2 else ' '} {'*' if fH else ' '}{fR,fC}{'t' if not step%2 else ' '}\n\nchose:{action}") ##############################################################################################
            self.filestream.write(str(self.tokensOnBoard))
            self.filestream.write('\n')
           #print(self.tokensOnBoard) ##############################################################################################
        
        if step%2:
            mR,mC,mH,fR,fC,fH, _,_,_,_,_,_ = self.currentState
        else:
            fR,fC,fH,mR,mC,mH, _,_,_,_,_,_ = self.currentState
        
        self.filestream.write(f"\n\nstep {step}:\n\t{'*' if mH else ' '}{mR,mC}{'t' if step%2 else ' '} {'*' if fH else ' '}{fR,fC}{'t' if not step%2 else ' '}\n{applicableActions}\nchose:{action}") ##############################################################################################
        board = [[0 for _ in range(5)] for _ in range(5)]
        board[mR][mC] = 'M'
        board[fR][fC] = 'F'
        self.filestream.write("\n"+str(np.array(board))+"\n")
        #end output

        # document action taken
        if step%2:
            self.maleRewards.append(getReward(action))
            self.maleStateActionRewardHistroy.append([startState, action, getReward(action)])
        else:
            self.femaRewards.append(getReward(action))
            self.femaStateActionRewardHistory.append([startState, action, getReward(action)])
        self.actionList.append(action)

        # update qTable (i.e. learn)
        updateQtable(step, startState, action)

        # prepare for next step by swapping currentAgent and otherAgent row,col,holding
        self.stepCounter += 1
        nextStepsState = list(self.currentState)
        nextStepsState[:3], nextStepsState[3:6] = nextStepsState[3:6], nextStepsState[:3]
        self.currentState = tuple(nextStepsState)

    def experiment1(self, subExperiment):
        print("Running Experiment 1 for 500 steps:", "\n", "-----------------------------------")

        for step in range(500):
            male = step%2
            self.POLICY(step, "PRANDOM")

        if subExperiment == 'a':
            self.experiment1_a()
        elif subExperiment == 'b':
            self.experiment1_b()
        elif subExperiment == 'c':
            self.experiment1_c()
        else:
            print("You're trying to run experiment 1, but you need to specify which subExperiment.")

    def experiment1_a(self):
        print("Running Experiment 1a for 7500 steps:", "\n", "-----------------------------------")
        for step in range(7500):
            self.POLICY(step, "PRANDOM")
        

    def experiment1_b(self):
        print("Running Experiment 1b for 7500 steps:", "\n", "-----------------------------------")
        terminalStatesReached = self.terminalStatesReached
        for step in range(7500):
            self.POLICY(step, "PGREEDY")

    def experiment1_c(self):
        print("Running Experiment 1c for 7500 steps:", "\n", "-----------------------------------")
        for step in range(7500):
            self.POLICY(step, "PEXPLOIT")

    def experiment2(self):
        print("Running Experiment 2 for 8000 steps:", "\n", "-----------------------------------")
        for step in range(500):
            self.POLICY(step, "PRANDOM")
        for step in range(7500):
            self.POLICY(step, "PGREEDY")

    def experiment3(self):
        print(f"Running Experiment 3 with alpha={self.learning_rate}:", "\n", "-----------------------------------")
        for step in range(500):
            self.POLICY(step, "PRANDOM")

        for step in range(7500):
            self.POLICY(step, "PEXPLOIT")

    def experiment4(self):
        print("Running Experiment 4:", "\n", "-----------------------------------")
        for step in range(500):
            self.POLICY(step, "PRANDOM")
        countStepsTerminateThree = 0
        countStepsTerminateSix = 0

        for step in count():
            countStepsTerminateThree += 1
            self.POLICY(step, "PEXPLOIT")
            if self.terminalStatesReached == 3:
                break

        pickupQvalue_3_1 = self.qTable[(3,1)].pop("pickUp")
        pickupQvalue_2_4 = self.qTable[(2,4)].pop("pickUp")
        self.pickUpCells = set([(0, 1), (3, 4)])
        self.resetWorld()
        self.qTable[(0,1)]["pickUp"] = pickupQvalue_3_1
        self.qTable[(3,4)]["pickUp"] = pickupQvalue_2_4
        for step in count():
            countStepsTerminateSix += 1
            self.POLICY(step, "PEXPLOIT")
            if self.terminalStatesReached == 6:
                break

    def resetWorld(self):
        self.tokensOnBoard = np.array([
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ])
        for pickUpCell in self.pickUpCells:
            self.tokensOnBoard[pickUpCell] = self.pickUpCellsStartWith
        self.malePos = np.array([4, 2])  # initial location of male agent
        self.femaPos = np.array([0, 2])  # initial location of fema agent


    def getActionList(self):
        maleActions = [i[1] for i in self.maleStateActionRewardHistroy]
        femaActions = [i[1] for i in self.femaStateActionRewardHistory]
        return list(np.array(list(zip(femaActions, maleActions))).reshape(-1)) # zips then flattens

    def visualize_steps_per_terminal_state(self):
        y = self.stepsPerTerminalState
        x = range(1,len(y)+1)
        title = f"{self.experimentName}\nSteps per Terminal State"
        # sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Steps")
        plot = sb.lineplot(x=x, y=y, marker = 'o').set(title=title, xlabel="Terminal State", ylabel="Steps")
        plt.show()
    
    def visualize_rewards_per_terminal_state(self):
        maleRewardsPerTerminalState = self.MReward
        femaRewardsPerTerminalState = self.FReward
        y = np.array(maleRewardsPerTerminalState) + np.array(femaRewardsPerTerminalState)
        x = range(1,len(y)+1)
        title = f"{self.experimentName}\nRewards per Terminal State"
        # sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Rewards for both Agents")
        sb.lineplot(x=x, y=y, marker = 'o').set(title=title, xlabel="Terminal State", ylabel="Rewards for both Agents")
        plt.show()

