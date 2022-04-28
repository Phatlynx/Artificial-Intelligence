from itertools import count
import random
import numpy as np
import seaborn as sb
import matplotlib.pyplot as plt


class experiment:
    def __init__(self, experiment, subExperiment=None, SARSA=False, seed=None, hivemind=True):
        self.experiment = experiment
        self.subExperiment = subExperiment
        self.hivemind = hivemind
        self.seed = seed
        random.seed(seed)  # for reproducibility
        np.random.seed(seed)
        #self.filestream = open("allSteps.txt", "w")
        self.experimentName = f"Experiment {str(experiment)}"
        if subExperiment != None:
            self.experimentName += f"{subExperiment}"
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

        self.maleRewardsPerStep = []  # rewards per step for male in current episode
        self.femaleRewardsPerStep = []  # rewards per step for female in current pisode

        self.maleRewardsPerEpisode = []  # stores total rewards for male in each episode
        self.femaleRewardsPerEpisode = []  # stores total rewards for female in each episode
        self.totalRewardsPerEpisode = [] # stores the total rewards for both male and female earned in each episode

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
        self.stepsPerTerminalState = []
        self.actionList = []

        self.manhattanDistance = [] # stores manhatten distance for current episode and get reset after reaching terminal state
        self.manhattanDistancePerState = []  # stores manhatten distance for all terminal states
        self.blockCounts = 0  # counts how many times agent block each other
        self.closeToEachOther = []  # when manhattan distance is 1 they are closest

        # tuples represent gameboard positions
        # strings represent movement actions
        # outer lists are indexed based on holding status
        # inner lists are indexed based on getPickUpIndex() and getDropOffIndex() respectively
        self.qTable = {
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

        self.qTable_ = {
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

        # a) when the first drop-off location is filled (the fifth block has been delivered to it)
        self.situation_a_not_yet_encountered = True
        self.converted_qTables_situation_a = None #female=index0, male=index1
        self.firstFilledDropOffLocation = None
        self.situation_a_agentPositions = None
        self.situation_a_agentHoldings = None
        self.situation_a_pickUpIndexStatus = None
        self.situation_a_step = None

        # b) when a terminal state is (first) reached
        self.situation_b_not_yet_encountered = True
        self.converted_qTables_situation_b = None
        self.situation_b_agentPositions = None
        self.situation_b_agentHoldings = None
        self.situation_b_step = None

        # c) the final Q-table of each experiment
        self.converted_qTables_situation_c = None
        self.situation_c_agentPositions = None
        self.situation_c_agentHoldings = None
        self.situation_c_pickUpIndexStatus = None
        self.situation_c_dropOffIndexStatus = None

        self.resetWorld()
        self.SARSA = SARSA
        self.hivemind = hivemind
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
        
        self.totalRewardsPerEpisode = list(np.array(self.maleRewardsPerEpisode)+np.array(self.femaleRewardsPerEpisode))
        
        # situation c
        PUi, DOi = self.getPickUpIndex(), self.getDropOffIndex()
        self.converted_qTables_situation_c = [self.convert_qTable(self.femaleHolding, PUi, DOi), self.convert_qTable(self.maleHolding, PUi, DOi)]
        self.situation_c_agentPositions =  [tuple(self.femalePos), tuple(self.malePos)]
        self.situation_c_agentHoldings = [self.femaleHolding, self.maleHolding]
        self.situation_c_pickUpIndexStatus = PUi
        self.situation_c_dropOffIndexStatus = DOi
        #self.filestream.close()


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
            self.maleRewardsPerStep.append(self.getRewards((row, col), holding))  # adding rewards for male
        else:
            self.femaleHolding = True
            self.femaleRewardsPerStep.append(self.getRewards((row, col), holding))  # adding rewards female
        self.board[row, col] -= 1
        #print(self.board)
        self.actionList.append('pickUp')

    def dropOff(self, male, row, col, holding):
        if male:
            if self.maleHolding:
                self.maleHolding = False
                self.board[row, col] += 1
                self.maleRewardsPerStep.append(self.getRewards((row, col), holding))  # adding rewards for male
                self.actionList.append('dropOff')
        else:  # must be female
            if self.femaleHolding:
                self.femaleHolding = False
                self.board[row, col] += 1
                self.femaleRewardsPerStep.append(self.getRewards((row, col), holding))  # adding rewards female
                self.actionList.append('dropOff')

    def nextPosition(self, male, directionsToTry, holding, qTableIndex):  # this is used to verify that the agents aren't going to occupy the same position
        i = 0
        #directionsToTry = [directionsToTry[0]] + random.sample(directionsToTry[1:], len(directionsToTry[1:])) # better than shuffling outside of the function
        if male:
            reward = self.getRewards(self.malePos, holding)
            self.maleRewardsPerStep.append(reward)  # adding rewards for male
            oldPos = self.malePos
            if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                i += 1
            newPos = oldPos + self.directionOffset[directionsToTry[i]]
            while (newPos == self.femalePos).all():  # male's new position can't be the same as the female's position, while it is, recalculate
                i += 1
                self.blockCounts += 1
                if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                    i += 1
                newPos = oldPos + self.directionOffset[directionsToTry[i]]
            self.maleStateMovementRewardHoldingHistroy.append([oldPos, directionsToTry[i], reward, holding, qTableIndex])
            self.malePos = newPos
        else:
            reward = self.getRewards(self.femalePos, holding)
            self.femaleRewardsPerStep.append(reward)  # adding rewards female
            oldPos = self.femalePos
            if directionsToTry[i] == 'dropOff' or directionsToTry[i] == 'pickUp':
                i += 1
            newPos = oldPos + self.directionOffset[directionsToTry[i]]
            while (newPos == self.malePos).all():  # female's new position can't be the same as the male's position, while it is, recalculate
                i += 1
                self.blockCounts += 1
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
            self.maleRewardsPerEpisode.append(sum(self.maleRewardsPerStep))  # adding sum of male reward from current terminal state
            self.maleRewardsPerStep = []  # initializing male reward to 0
            self.femaleRewardsPerEpisode.append(sum(self.femaleRewardsPerStep))  # adding sum of female reward from current terminal state
            self.femaleRewardsPerStep = []  # initializing female reward to 0
            self.stepsPerTerminalState.append(self.stepCounter)
            self.stepCounter = 0
            self.manhattanDistancePerState.append(self.manhattanDistance)
            self.closeToEachOther.append(self.manhattanDistance.count(1))
            self.manhattanDistance = []
            self.resetWorld()
        if self.situation_b_not_yet_encountered and self.terminalStatesReached == 1: # save converted q table for situation b
            self.situation_b_not_yet_encountered = False
            self.situation_b_step = step
            PUi, DOi = self.getPickUpIndex(), self.getDropOffIndex()
            self.converted_qTables_situation_b = [self.convert_qTable(self.femaleHolding, PUi, DOi), self.convert_qTable(self.maleHolding, PUi, DOi)]
            self.situation_b_agentPositions =  [tuple(self.femalePos), tuple(self.malePos)]
            self.situation_b_agentHoldings = [self.femaleHolding, self.maleHolding]
            if self.experiment == 2 and self.seed == 577:
                    self.output_qTable(f"experiment_{self.experiment}_{self.subExperiment}_{self.seed}_qTable_situation_b.txt")
            del PUi, DOi
        self.stepCounter += 1
        male, row, col, holding = self.maleRowColHolding(step)  # uses step count to determine which players turn it is and the position of that player
        self.manhattanDistance.append(self.manhattan(self.malePos, self.femalePos) if male else self.manhattan(self.femalePos, self.malePos))
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
            DOi = self.getDropOffIndex()
            if self.situation_a_not_yet_encountered and 10 < DOi < 15 and self.terminalStatesReached < 1: # save converted q tables for situation a
                self.situation_a_not_yet_encountered = False
                self.situation_a_step = step
                if DOi == 11 and self.firstFilledDropOffLocation == None:
                    self.firstFilledDropOffLocation = self.dropOffCells[4-1] #dropOff4
                if DOi == 12 and self.firstFilledDropOffLocation == None:
                    self.firstFilledDropOffLocation = self.dropOffCells[3-1] #dropOff3
                if DOi == 13 and self.firstFilledDropOffLocation == None:
                    self.firstFilledDropOffLocation = self.dropOffCells[2-1] #dropOff2
                if DOi == 14 and self.firstFilledDropOffLocation == None:
                    self.firstFilledDropOffLocation = self.dropOffCells[1-1] #dropOff1
                PUi = self.getPickUpIndex()
                self.converted_qTables_situation_a = [self.convert_qTable(self.femaleHolding, PUi, DOi), self.convert_qTable(self.maleHolding, PUi, DOi)]
                self.situation_a_agentPositions = [tuple(self.femalePos), tuple(self.malePos)]
                self.situation_a_agentHoldings = [self.femaleHolding, self.maleHolding]
                self.situation_a_pickUpIndexStatus = PUi
                if self.experiment == 2 and self.seed == 577:
                    self.output_qTable(f"experiment_{self.experiment}_{self.subExperiment}_{self.seed}_qTable_situation_a.txt")

        else:  # else make a move
            if policy == "PRANDOM":
                directionsToTry = random.sample(list(self.qTable[(row, col)].keys()) if self.hivemind or male else list(self.qTable_[(row, col)].keys()),
                    len(self.qTable[(row, col)]) if self.hivemind else len(self.qTable_[(row, col)]))  # directions ordered randomly
                nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
            elif policy == "PGREEDY":
                directionsToTry = sorted(self.qTable[(row, col)] if self.hivemind or male else self.qTable_[(row, col)] , key=lambda i: self.qTable[(row, col)][i][holding][
                    self.getDropOffIndex() if holding else self.getPickUpIndex()] if self.hivemind or male else self.qTable_[(row, col)][i][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()],
                        reverse=True)  # directions ordered best to worst
                nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())

            elif policy == "PEXPLOIT":
                decideWhich = np.random.uniform()
                if decideWhich < 0.8:
                    directionsToTry = sorted(self.qTable[(row, col)] if self.hivemind or male else self.qTable_[(row, col)],
                        key=lambda i: self.qTable[(row, col)][i][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] if self.hivemind or male else
                        self.qTable_[(row, col)][i][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()], reverse=True)  # directions ordered best to worst
                    nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
                else:
                    directionsToTry = random.sample(list(self.qTable[(row, col)].keys()) if self.hivemind or male else list(self.qTable_[(row, col)].keys()),
                        len(self.qTable[(row, col)]) if self.hivemind or male else len(self.qTable_[(row, col)]))  # directions ordered randomly
                    nextDirection = self.nextPosition(male, directionsToTry, holding, self.getDropOffIndex() if holding else self.getPickUpIndex())
            else:
                print("Incorrect specification of policy name. Should be 'PRANDOM', 'PGREEDY', or 'PEXPLOIT'")

        #self.filestream.write(f"PUi:{self.getPickUpIndex()}\t\tDOi:{self.getDropOffIndex()}\n")
        #self.filestream.write(f"---{self.actionList[-1]}---\n")
        oldPos = (row, col)  # curent position coordinates
        curPos = tuple(self.malePos) if male else tuple(self.femalePos)  # next position coordinates
        Qtable = self.qTable if self.hivemind or male else self.qTable_
        self.updateQtable(curPos, oldPos, nextDirection, male, holding, step, Qtable)  # updating qTable



        

    def updateQtable(self, nextpos, currPos, direction, male, holding, step, Qtable):  # update q table for every move regardless of agent FOR CURRENT POSITION
        if step >= 2 and self.SARSA:
            S, oldMove, oldReward, oldHolding, old_qTableIndex = self.maleStateMovementRewardHoldingHistroy[-2] if male else self.femaleStateMovementRewardHoldingHistory[-2]
            S = tuple(S)
            Qtable[S][oldMove][oldHolding][old_qTableIndex] += \
                self.learning_rate * \
                    (oldReward + \
                    self.discount_factor * Qtable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] - \
                    Qtable[S][oldMove][oldHolding][old_qTableIndex])
        else:
            # getting max q-value from next position
            Qtable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] += \
                self.learning_rate * \
                    (self.getRewards(currPos, holding) + \
                    self.discount_factor * max([val[holding][self.getDropOffIndex() if holding else self.getPickUpIndex()] for val in Qtable[nextpos].values()]) - \
                    Qtable[currPos][direction][holding][self.getDropOffIndex() if holding else self.getPickUpIndex()])

    def experiment1(self, subExperiment):
        terminalStatesReached = self.terminalStatesReached
        for step in range(500):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

        if subExperiment == 'a':
            self.experiment1_a()
        elif subExperiment == 'b':
            self.experiment1_b()
        elif subExperiment == 'c':
            self.experiment1_c()
        else:
            print("You're trying to run experiment 1, but you need to specify which subExperiment.")

    def experiment1_a(self):
        print("Experiment 1a ", end="")
        terminalStatesReached = self.terminalStatesReached
        for step in range(500,8000):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

    def experiment1_b(self):
        print("Experiment 1b ", end="")
        terminalStatesReached = self.terminalStatesReached
        for step in range(500,8000):
            male, _, _, holding = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step+500}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PGREEDY")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

    def experiment1_c(self):
        print("Experiment 1c ", end="")
        terminalStatesReached = self.terminalStatesReached
        for step in range(500,8000):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PEXPLOIT")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

    def experiment2(self):
        terminalStatesReached = self.terminalStatesReached
        print("Experiment 2 ", end="")
        for step in range(500):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached
        for step in range(500,8000):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PEXPLOIT")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached


    def experiment3(self):
        print(f"Experiment 3 with alpha={self.learning_rate} ", end="")
        terminalStatesReached = self.terminalStatesReached
        for step in range(500):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

        for step in range(500,8000):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PEXPLOIT")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached

    def experiment4(self):
        terminalStatesReached = self.terminalStatesReached
        print("Experiment 4 ", end="")
        for step in range(500):
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PRANDOM")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached
        countStepsTerminateThree = 0
        countStepsTerminateSix = 0

        for step in count():
            countStepsTerminateThree += 1
            male, _, _, _ = self.maleRowColHolding(step)
            #self.filestream.write(f"\n{step}:\nmale:{'*' if self.maleHolding else ''}{self.malePos}{'t' if male else ''}\t\tfem:{'*' if self.femaleHolding else ''}{self.femalePos}{'t' if not male else ''}\n")
            self.POLICY(step, "PEXPLOIT")
            #self.filestream.write(str(self.board))
            #self.filestream.write('\n')
            #if terminalStatesReached != self.terminalStatesReached:
            #    self.filestream.write(f"=====================TERMINAL STATE {self.terminalStatesReached}==========================\n")
            #    terminalStatesReached = self.terminalStatesReached
            if self.terminalStatesReached == 3:
                break

        self.qTable[(3, 1)].pop("pickUp")
        self.qTable[(2, 4)].pop("pickUp")
        self.pickUpCells = set([(0, 1), (3, 4)])
        self.resetWorld()
        self.qTable[(0, 1)]["pickUp"] = [[0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
        self.qTable[(3, 4)]["pickUp"] = [[0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
        if not self.hivemind:
            self.qTable_[(3, 1)].pop("pickUp")
            self.qTable_[(2, 4)].pop("pickUp")
            self.qTable_[(0, 1)]["pickUp"] = [[0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
            self.qTable_[(3, 4)]["pickUp"] = [[0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
        for step in count():
            countStepsTerminateSix += 1
            self.POLICY(step, "PEXPLOIT")
            if self.terminalStatesReached == 6:
                break

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
            return 3 # both have tokens
        else:  # not both
            if pickUp2:
                return 2  # only (3,1) has tokens
            elif pickUp1:
                return 1 # only (2,4) has tokens
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
        for pos in self.qTable.keys():
            for direction in self.qTable[pos].keys():
                for holding in [0, 1]:
                    if self.qTable[pos][direction][holding] != self.qTable_[pos][direction][holding]:
                        print(
                            f"qTable[{pos}][{direction}][{holding}]={self.qTable[pos][direction][holding]} != {self.qTable_[pos][direction][holding]} = qTable_[{pos}][{direction}][{holding}]")
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
        # sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Steps")
        plot = sb.lineplot(x=x, y=y, marker = 'o').set(title=title, xlabel="Terminal State", ylabel="Steps")
        plt.show()
    
    def visualize_rewards_per_terminal_state(self):
        maleRewardsPerTerminalState = self.maleRewardsPerEpisode
        femaleRewardsPerTerminalState = self.femaleRewardsPerEpisode
        y = np.array(maleRewardsPerTerminalState) + np.array(femaleRewardsPerTerminalState)
        x = range(1,len(y)+1)
        title = f"{self.experimentName}\nRewards per Terminal State"
        # sb.scatterplot(x=x, y=y).set(title=title, xlabel="Terminal State", ylabel="Rewards for both Agents")
        sb.lineplot(x=x, y=y, marker = 'o').set(title=title, xlabel="Terminal State", ylabel="Rewards for both Agents")
        plt.show()

    def output_qTable(self, fileName='qTable.txt'):
        with open(fileName, 'w') as f:
            # make all states
            states = [(r,c,h,p_s,d_s) for r in range(5) for c in range(5) for h in [False,True] for p_s in range(4) for d_s in range(16)]
            actions = ["north", "east", "south", "west"]
            qTable = {state:{action:self.qTable[state[:2]][action][state[2]][state[4] if state[2] else state[3]] if action in self.qTable[state[:2]] else 0 
                        for action in actions} 
                            for state in states}
            f.write("r = row, c = col, h = holdingStatus, pi = pickupIndex, di = dropOffIndex\n")
            f.write(f"{'states':^20s}{'actions':^40s}\n")  
            f.write(f"{' r, c,  h,   pi, di':20s}{'north':>10s}{'east':>10s}{'south':>10s}{'west':>10s}\n")
            for state in states:
                north,east,south,west = f"{qTable[state]['north']:.3f}",f"{qTable[state]['east']:.3f}",f"{qTable[state]['south']:.3f}",f"{qTable[state]['west']:.3f}"
                f.write(f"{str(state):20s}{north:>10s}{east:>10s}{south:>10s}{west:>10s}\n")

    def convert_qTable(self, holding, pickUpStatus, dropOffStatus):
        #actionOrder = ["north", "east", "south", "west"]
        north, east, south, west = np.empty((5,5)),np.empty((5,5)),np.empty((5,5)),np.empty((5,5))
        for pos in self.qTable:
            #if the movement action is in the qTable for that state, then add it its list, otherwise
            north[pos] = self.qTable[pos]["north"][holding][dropOffStatus if holding else pickUpStatus] if "north" in self.qTable[pos] else 0
            east[pos] = self.qTable[pos]["east"][holding][dropOffStatus if holding else pickUpStatus] if "east" in self.qTable[pos] else 0
            south[pos] = self.qTable[pos]["south"][holding][dropOffStatus if holding else pickUpStatus] if "south" in self.qTable[pos] else 0
            west[pos] = self.qTable[pos]["west"][holding][dropOffStatus if holding else pickUpStatus] if "west" in self.qTable[pos] else 0
        return [north, east, south, west]

    def manhattan(self, a, b):
        return sum(abs(val1 - val2) for val1, val2 in zip(a, b))
