from itertools import count
import random
import numpy as np
import seaborn as sb
import matplotlib.pyplot as plt

seed = 1  # np.random.randint(0,1000)
random.seed(seed)  # for reproducibility
np.random.seed(seed)


class experiment:
    def __init__(self, experiment, subExperiment=None, SARSA=False):
        self.filestream = open("allSteps.txt", "w")
        self.board = np.array([
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
        self.femaleHolding = False

        self.malePos = np.array([4, 2])  # initial location of male agent
        self.femalePos = np.array([0, 2])  # initial location of female agent

        self.maleRewards = []  # rewards for male for each stage
        self.femaleRewards = []  # rewards for female for each stage

        self.MReward = []  # stores total rewards for male to reach each terminal stage
        self.FReward = []  # stores total rewards for female to reach each terminal stage

        # these next two are list of lists where each inner list is a nupy array representing position, a string representing the movement-action taken in that position, and the reward for that movement - just had to change the nextPosition function to implement updates
        # these are used for SARSA
        self.maleStateMovementRewardHoldingHistroy = []
        self.femaleStateMovementRewardHoldingHistory = []
        # if it turns out our qTable needs to have actions for pickUp and dropOff then these lists need to shift to represent all actions (not just movement actions) and the pickUp and dropOff functiosn will have to be changed

        self.directionOffset = {"north": np.array([-1, 0]), "south": np.array([1, 0]), "east": np.array([0, 1]),"west": np.array([0, -1])}

        self.learning_rate = None
        self.discount_factor = None
        self.SARSA = None
        self.terminalStatesReached = 0
        self.stepOfLastTerminalState = 0
        self.stepsPerTerminalState = []
        self.actionList = []

        # tuples represent gameboard positions
        # strings represent movement actions
        # outer lists are indexed based on holding status
        # inner lists are indexed based on getPickUpIndex() and getDropOffIndex() respectively
        regularQtable = {
            (0, 0): {"south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (0, 1): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (0, 2): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (0, 3): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (0, 4): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "pickUp":  [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (3, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (3, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "pickUp":  [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (3, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (3, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (3, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],            
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (4, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (4, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]}
            }

        negInfsQtable = {
            (0, 0): {"south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[-float('inf')]*4, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (0, 2): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (0, 3): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (0, 1): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (0, 4): {"west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[-float('inf')]*4, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (1, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[-float('inf')]*4, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (2, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "pickUp":  [[0,0,0,0], [-float('inf')]*16]},
            
            (3, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            
            (3, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "pickUp":  [[0,0,0,0], [-float('inf')]*16]},
            
            (3, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (3, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "south":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (3, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 0): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],            
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (4, 1): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 2): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
                     
            (4, 3): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "east":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},

            (4, 4): {"north":   [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "west":    [[0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
                     "dropOff": [[-float('inf')]*4, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]}
            }
        
        oldQtable = { 
            (0,0):{"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (0,2):{"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (0,3):{"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (0,1):{"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (0,4):{"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (1,0):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (1,1):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (1,2):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (1,3):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (1,4):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (2,0):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (2,1):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (2,2):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (2,3):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (2,4):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (3,0):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (3,1):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]], "west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (3,2):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]], "west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (3,3):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"south":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]], "west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (3,4):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (4,0):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (4,1):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (4,2):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (4,3):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"east":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]},
            (4,4):{"north":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],"west":[[0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]}        }

        self.qTable = regularQtable
        #self.qTable = negInfsQtable
        self.qTableNoPUDO = oldQtable

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


    def maleRowColHolding(self,step):  # based on step count, determine whose turn it is, their position on the gameboard, and whether they're holding
        if step % 2 == 1:
            male = True
            row = self.malePos[0]
            col = self.malePos[1]
            holding = self.maleHolding
        else:
            male = False
            row = self.femalePos[0]
            col = self.femalePos[1]
            holding = self.femaleHolding
        return male, row, col, holding

    def pickUp(self, male, row, col, holding):
        if male:
            self.maleHolding = True
            self.maleRewards.append(self.getRewards((row, col), holding))  # adding rewards for male
        else:
            self.femaleHolding = True
            self.femaleRewards.append(self.getRewards((row, col), holding))  # adding rewards female
        self.board[row, col] -= 1
        #print(self.board)
        self.actionList.append('pickUp')

    def dropOff(self, male, row, col, holding):
        if male:
            if self.maleHolding:
                self.maleHolding = False
                self.board[row, col] += 1
                self.maleRewards.append(self.getRewards((row, col), holding))  # adding rewards for male
                self.actionList.append('dropOff')
        else:  # must be female
            if self.femaleHolding:
                self.femaleHolding = False
                self.board[row, col] += 1
                self.femaleRewards.append(self.getRewards((row, col), holding))  # adding rewards female
                self.actionList.append('dropOff')
        #print(self.board)

    def nextPosition(self, male, directionsToTry, holding, qTableIndex):  # this is used to verify that the agents aren't going to occupy the same position
        i = 0
        #directionsToTry = [directionsToTry[0]] + random.sample(directionsToTry[1:], len(directionsToTry[1:])) # better than shuffling outside of the function
        if male:
            reward = self.getRewards(self.malePos, holding)
            self.maleRewards.append(reward)  # adding rewards for male
            oldPos = self.malePos
            if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                i += 1
            newPos = oldPos + self.directionOffset[directionsToTry[i]]
            #directionsToTry = random.sample(directionsToTry[1:],len(directionsToTry[1:])) ##############################################################
            while (newPos == self.femalePos).all():  # male's new position can't be the same as the female's position, while it is, recalculate
                i += 1
                if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                    i += 1
                newPos = oldPos + self.directionOffset[directionsToTry[i]]
            self.maleStateMovementRewardHoldingHistroy.append([oldPos, directionsToTry[i], reward, holding, qTableIndex])
            self.malePos = newPos
        else:
            reward = self.getRewards(self.femalePos, holding)
            self.femaleRewards.append(reward)  # adding rewards female
            oldPos = self.femalePos
            if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                i += 1
            newPos = oldPos + self.directionOffset[directionsToTry[i]]
            # directionsToTry = random.sample(directionsToTry[1:],len(directionsToTry[1:])) #########################################################
            while (newPos == self.malePos).all():  # female's new position can't be the same as the male's position, while it is, recalculate
                i += 1
                if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                    i += 1
                newPos = oldPos + self.directionOffset[directionsToTry[i]]
            self.femaleStateMovementRewardHoldingHistory.append([oldPos, directionsToTry[i], reward, holding, qTableIndex])
            self.femalePos = newPos

        self.actionList.append(directionsToTry[i])
        return directionsToTry[i]

    def POLICY(self, step: int, policy: str):
        if self.terminalState():
            self.terminalStatesReached += 1
            #print(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================")
            self.MReward.append(sum(self.maleRewards))  # adding sum of male reward from current terminal state
            self.maleRewards = []  # initializing male reward to 0
            self.FReward.append(sum(self.femaleRewards))  # adding sum of female reward from current terminal state
            self.femaleRewards = []  # initializing female reward to 0
            self.stepsPerTerminalState.append(self.stepCounter)
            self.stepCounter = 0
            self.resetWorld()
        self.stepCounter += 1
        male, row, col, holding = self.maleRowColHolding(step)  # uses step count to determine which players turn it is and the position of that player
        if not holding and (row, col) in self.pickUpCells and self.board[row, col] > 0:  # if we can pick up then do so
            self.pickUp(male, row, col, holding)
            nextDirection = 'pickUp'
            if not male:
                self.femaleStateMovementRewardHoldingHistory.append([(row, col), 'pickUp', self.getRewards((row, col), holding), holding, self.getDropOffIndex() if holding else self.getPickUpIndex()])
            else:
                self.maleStateMovementRewardHoldingHistroy.append([(row, col), 'pickUp', self.getRewards((row, col), holding), holding, self.getDropOffIndex() if holding else self.getPickUpIndex()])
        elif (row, col) in self.dropOffCells and self.board[row, col] < 5 and ((male and self.maleHolding) or (not male and self.femaleHolding)):  # else if we can drop off then do so:  # else if we can drop off then do so
            self.dropOff(male, row, col, holding)
            nextDirection = 'dropOff'
            if not male:
                self.femaleStateMovementRewardHoldingHistory.append([(row, col), 'dropOff', self.getRewards((row, col), holding), holding, self.getDropOffIndex() if holding else self.getPickUpIndex()])
            else:
                self.maleStateMovementRewardHoldingHistroy.append([(row, col), 'dropOff', self.getRewards((row, col), holding), holding, self.getDropOffIndex() if holding else self.getPickUpIndex()])
        else:  # else make a move
            if policy == "PRANDOM":
                directionsToTry = random.sample(list(self.qTable[(row, col)].keys()), len(self.qTable[(row, col)]))  # directions ordered randomly
                nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
            elif policy == "PGREEDY":
                directionsToTry = sorted(self.qTable[(row, col)], key=lambda i: self.qTable[(row, col)][i][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()], reverse=True)  # directions ordered best to worst
                
                for action in directionsToTry:
                    self.filestream.write(f"{action}: {self.qTable[(row, col)][action][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()]}\n")
    
                if directionsToTry[0] == "pickUp" or directionsToTry[0] == "dropOff":
                    directionsToTry = directionsToTry[1:]
                #directionsToTry = [directionsToTry[0]] + random.sample(directionsToTry[1:], len(directionsToTry[1:])) # better to do this inside of nextPosition
                #if 4050 < step+500 < 4550:
                #    print(male, self.malePos if male else self.femalePos, directionsToTry) #################################################################################################
                nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
            elif policy == "PEXPLOIT":
                decideWhich = np.random.uniform()
                if decideWhich < 0.8:
                    directionsToTry = sorted(self.qTable[(row, col)], key=lambda i: self.qTable[(row, col)][i][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()], reverse=True)
                    #directionsToTry = [directionsToTry[0]] + random.sample(directionsToTry[1:], len(directionsToTry[1:])) # all but first direciton are randomly ordered
                    nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
                else:
                    directionsToTry = random.sample(list(self.qTable[(row, col)].keys()), len(self.qTable[(row, col)]))  # use q-values to decide which direction to move
                    nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
            else:
                print("Incorrect specification of policy name. Should be 'PRANDOM', 'PGREEDY', or 'PEXPLOIT'")
            #if (holding and directionsToTry[0] == "pickUp") or (not holding and directionsToTry[0] == "dropOff"):
             #   print(f"Step {step}: {'male' if male else 'female'} was {'holding' if holding else 'not holding'} but the first action they tried was: {directionsToTry[0]}")

        self.filestream.write(f"PUi:{self.getPickUpIndex()}\t\tDOi:{self.getDropOffIndex()}\n")
        self.filestream.write(f"---{self.actionList[-1]}---\n")
        oldPos = (row, col)  # curent position coordinates
        curPos = tuple(self.malePos) if male else tuple(self.femalePos)  # next position coordinates
        # self.updateQtable_(curPos, oldPos, nextDirection, step)
        self.updateQtable(curPos, oldPos, nextDirection, male, holding, step)  # updating qTable
        if not self.qTablesAreSame():
            print(step)
            exit()
        # print("from policy: " + str(step) + " " + str(holding))
        

    def updateQtable(self, nextpos, currPos, direction, male, holding, step):  # update q table for every move regardless of agent FOR CURRENT POSITION
        if step >= 2 and self.SARSA:
            S, oldMove, oldReward, oldHolding, old_qTableIndex = self.maleStateMovementRewardHoldingHistroy[-2] if male else self.femaleStateMovementRewardHoldingHistory[-2]
            S = tuple(S)
            self.qTable[S][oldMove][oldHolding][old_qTableIndex] += \
                self.learning_rate * \
                    (oldReward + \
                    self.discount_factor * self.qTable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] - \
                    self.qTable[S][oldMove][oldHolding][old_qTableIndex])
            
            if direction != "pickUp" and direction != "dropOff":
                self.qTableNoPUDO[S][oldMove][oldHolding][old_qTableIndex] += \
                    self.learning_rate * \
                        (oldReward + \
                        self.discount_factor * self.qTableNoPUDO[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] - \
                        self.qTableNoPUDO[S][oldMove][oldHolding][old_qTableIndex])
        else:
            # getting max q-value from next position
            self.qTable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] += \
                self.learning_rate * \
                    (self.getRewards(currPos, holding) + \
                    self.discount_factor * max([val[holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] for val in self.qTable[nextpos].values()]) - \
                    self.qTable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()])
            
            if direction != "pickUp" and direction != "dropOff":
                self.qTableNoPUDO[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] += \
                    self.learning_rate * \
                        (self.getRewards(currPos, holding) + \
                        self.discount_factor * max([val[holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] for val in self.qTableNoPUDO[nextpos].values()]) - \
                        self.qTableNoPUDO[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()])

    def experiment1(self, subExperiment):
        print("Running Experiment 1 for 500 steps:", "\n", "-----------------------------------")

        terminalStatesReached = self.terminalStatesReached
        for step in range(500):
            male, _, _, _ = self.maleRowColHolding(step)
            self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            self.filestream.write(str(self.board))
            self.filestream.write('\n')
            if terminalStatesReached != self.terminalStatesReached:
                self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
                terminalStatesReached = self.terminalStatesReached

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
            male, _, _, holding = self.maleRowColHolding(step)
            self.filestream.write(f"\n{step+500}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PGREEDY")
            self.filestream.write(str(self.board))
            self.filestream.write('\n')
            if terminalStatesReached != self.terminalStatesReached:
                self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
                terminalStatesReached = self.terminalStatesReached

    def experiment1_c(self):
        print("Running Experiment 1c for 7500 steps:", "\n", "-----------------------------------")
        for step in range(7500):
            self.POLICY(step, "PEXPLOIT")

    def experiment2(self):
        # run Sarsa q-learning for 8000 steps
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
        # print("Number of steps taken to 6 terminal states:", countStepsTerminateSix)

    def terminalState(self):  # re-wrote this so that it's more flexible (for when we change drop-off and pick-up locations)
        if not self.maleHolding and not self.femaleHolding:  # both agents must not be holding in order to terminate
            # all dropOffCells should be full
            for cell in self.dropOffCells:  # for every cell in dropOffCells
                if self.board[cell] != self.dropOffCellCapacity:  # if it's not full then "return "False
                    return False
            # all pickUPCells should be empty
            for cell in self.pickUpCells:  # for every cellin pickUpCells
                if self.board[cell] != 0:  # if it's not empty then return False
                    return False
            return True  # both agents were empty handed, all dropOffCells were full and all pickUpCells were empty
        return False

    def resetWorld(self):
        self.board = np.array([
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ])
        for pickUpCell in self.pickUpCells:
            self.board[pickUpCell] = self.pickUpCellsStartWith
        self.malePos = np.array([4, 2])  # initial location of male agent
        self.femalePos = np.array([0, 2])  # initial location of female agent

    def getRewards(self, pos, holding):
        row, col = pos
        if holding:
            if (row, col) in self.dropOffCells and self.board[row, col] < 5:
                return 13
        elif (row, col) in self.pickUpCells and self.board[row, col] > 0:
            return 13
        return -1

    def getActionList(self):
        return self.actionList

    def getPickUpIndex(self):  # returns an index to access the array in the notHolding values
        # index is the index to [noMoreTokens, only (2,4) has tokens, only (3,1) has tokens, both have tokens]
        pickUp1, pickUp2 = self.pickUpCells  # positions
        pickUp1, pickUp2 = self.board[pickUp1], self.board[pickUp2]  # tokens left in each (used as bools)
        if pickUp1 and pickUp2:
            return 3
        else:  # not both
            if pickUp2:
                return 2
            elif pickUp1:
                return 1
            else:
                return 0

    def getDropOffIndex(self):  # dropOffCells = set([(0,0), (0,4), (2,2), (4,4)])
        dropOff1, dropOff2, dropOff3, dropOff4 = self.dropOffCells  # positions
        dropOff1, dropOff2, dropOff3, dropOff4 = self.board[dropOff1] < 5, self.board[dropOff2] < 5, self.board[dropOff3] < 5, self.board[dropOff4] < 5  # bools represent whether they can take more
        if not (dropOff1 or dropOff2 or dropOff3 or dropOff4):  # if all are full
            return 0
        else:  # at least one must not be full
            # this layer represents where only one is not full
            if dropOff1 and not (dropOff2 or dropOff3 or dropOff4):
                return 1
            elif dropOff2 and not (dropOff1 or dropOff3 or dropOff4):  # these indices aren't being returned 2,5,8
                return 2
            elif dropOff3 and not (dropOff1 or dropOff2 or dropOff4):
                return 3
            elif dropOff4 and not (dropOff1 or dropOff2 or dropOff3):
                return 4
            else:  # at least two must not be full
                if dropOff1 and dropOff2 and not (dropOff3 or dropOff4):
                    return 5
                elif dropOff1 and dropOff3 and not (dropOff2 or dropOff4):
                    return 6
                elif dropOff1 and dropOff4 and not (dropOff2 or dropOff3):
                    return 7
                elif dropOff2 and dropOff3 and not (dropOff1 or dropOff4):
                    return 8
                elif dropOff2 and dropOff4 and not (dropOff1 or dropOff3):
                    return 9
                elif dropOff3 and dropOff4 and not (dropOff1 or dropOff2):
                    return 10
                else:  # at least 3 must not be full
                    if dropOff1 and dropOff2 and dropOff3 and not dropOff4:
                        return 11
                    elif dropOff1 and dropOff2 and dropOff4 and not dropOff3:
                        return 12
                    elif dropOff1 and dropOff3 and dropOff4 and not dropOff2:
                        return 13
                    elif dropOff2 and dropOff3 and dropOff4 and not dropOff1:
                        return 14
                    else:  # all must not be full
                        return 15

    def qTablesAreSame(self):
        for pos in self.qTableNoPUDO.keys():
            for direction in self.qTableNoPUDO[pos].keys():
                for holding in [0, 1]:
                    if self.qTable[pos][direction][holding] != self.qTableNoPUDO[pos][direction][holding]:
                        print(
                            f"qTable[{pos}][{direction}][{holding}]={self.qTable[pos][direction][holding]} != {self.qTableNoPUDO[pos][direction][holding]} = qTableNoPUDO[{pos}][{direction}][{holding}]")
                        return False
        return True

    def print_qTable(self):
        for pos in self.qTable.keys():
            print(f"{pos}:")
            for direction in self.qTable[pos].keys():
                print(f"\t{direction}:")
                for holding in [False, True]:
                    print(
                        f"\t\t{'Agent is holding' if holding else 'Agent is not holding'}:{self.qTable[pos][direction][holding]}")

    def visualize_steps_per_terminal_state(self):
        y = self.stepsPerTerminalState
        x = range(1,len(y)+1)
        title = f"{self.experimentName}\nSteps per Terminal State"
        plot = sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Steps")
        plt.show()
    
    def visualize_rewards_per_terminal_state(self):
        maleRewardsPerTerminalState = self.MReward
        femaleRewardsPerTerminalState = self.FReward
        y = np.array(maleRewardsPerTerminalState) + np.array(femaleRewardsPerTerminalState)
        x = range(1,len(y)+1)
        title = f"{self.experimentName}\nRewards per Terminal State"
        plot = sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Rewards for both Agents")
        plt.show()

    def output_qTable(self, fileName='qTable.txt'):
        with open(fileName, 'w') as f:
            for pos in self.qTable.keys():
                f.write(f"{pos}:\n")
                for direction in self.qTable[pos].keys():
                    f.write(f"\t{direction}:\n")
                    for holding in [0, 1]:
                        f.write(f"\t\t{'Agent is holding' if holding else 'Agent is not holding'}:{self.qTable[pos][direction][holding]}\n")
    
    