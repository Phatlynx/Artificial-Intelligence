import argparse
from q_learning import *

def experiment_1_a_v0():
    exp = experiment(1,'a', seed=123, hivemind=False)
    print(exp.getActionList())
    return exp.getActionList()

def experiment_1_a_v1():
    exp = experiment(1,'a', seed=326, hivemind=False)
    print(exp.getActionList())
    return exp.getActionList()

def experiment_1_b_v0():
    exp = experiment(1,'b', seed=123, hivemind=False)
    return exp.getActionList()

def experiment_1_b_v1():
    exp = experiment(1,'b', seed=326, hivemind=False)
    return exp.getActionList()

def experiment_1_c_v0():
    exp = experiment(1,'c', seed=123, hivemind=False)
    return exp.getActionList()

def experiment_1_c_v1():
    exp = experiment(1,'c', seed=326, hivemind=False)
    return exp.getActionList()

def experiment_2_v0():
    exp = experiment(2, subExperiment=None, SARSA=True, seed=123, hivemind=False)
    return exp.getActionList()

def experiment_2_v1():
    exp = experiment(2, subExperiment=None, SARSA=True, seed=326, hivemind=False)
    return exp.getActionList()

def experiment_3_v0():
    exp = experiment(3, seed=123, hivemind=False)
    return exp.getActionList()

def experiment_3_v1():
    exp = experiment(3, seed=326, hivemind=False)
    return exp.getActionList()

def experiment_4_v0():
    exp = experiment(4, seed=123, hivemind=False)
    return exp.getActionList()

def experiment_4_v1():
    exp = experiment(4, seed=326, hivemind=False)
    return exp.getActionList()

######################################################################################################################

def create_list(exp_, exp_list):
    x = "\n".join(map(str, exp_list))
    with open(f'/Users/jxc/Desktop/Unity_projects/RL_v0/Assets/scripts/{exp_}.txt', 'w') as f:
        f.write(x)
        f.close()   

def create_exp_parser():
    parser = argparse.ArgumentParser(description = 'Choose which experiement to run.')
    parser.add_argument('exp_', type=str)
    return parser

######################################################################################################################

def controller(exp_):

    if(exp_=='exp_1a_v0'):
        exp1a_v0_list = experiment_1_a_v0()
        create_list(exp_, exp1a_v0_list)

    if(exp_=='exp_1a_v1'):
        exp1a_v1_list = experiment_1_a_v1()
        create_list(exp_, exp1a_v1_list)
       
    elif(exp_=='exp_1b_v0'):
        exp1b_v0_list = experiment_1_b_v0()
        create_list(exp_, exp1b_v0_list)

    elif(exp_=='exp_1b_v1'):
        exp1b_v1_list = experiment_1_b_v1()
        create_list(exp_, exp1b_v1_list)
    
    elif(exp_=='exp_1c_v0'):
        exp1c_v0_list = experiment_1_c_v0()
        create_list(exp_, exp1c_v0_list)
    
    elif(exp_=='exp_1c_v1'):
        exp1c_v1_list = experiment_1_c_v1()
        create_list(exp_, exp1c_v1_list)

    elif(exp_=='exp_2_v0'):
        exp2_v0_list = experiment_2_v0()
        create_list(exp_, exp2_v0_list)

    elif(exp_=='exp_2_v1'):
        exp2_v1_list = experiment_2_v1()
        create_list(exp_, exp2_v1_list)
    
    elif(exp_=='exp_3_v0'):
        exp3_v0_list = experiment_3_v0()
        create_list(exp_, exp3_v0_list)

    elif(exp_=='exp_3_v1'):
        exp3_v1_list = experiment_3_v1()
        create_list(exp_, exp3_v1_list)
    
    elif(exp_=='exp_4_v0'):
        exp4_v0_list = experiment_4_v0()
        create_list(exp_, exp4_v0_list)

    elif(exp_=='exp_4_v1'):
        exp4_v1_list = experiment_4_v1()
        create_list(exp_, exp4_v1_list)
    
    else:
        print("No experiement selected. Please pick an experiment and run again.")

######################################################################################################################

def main(args):
    print(args.exp_)
    controller(args.exp_)
    
if __name__ == '__main__':

    parser = create_exp_parser()
    args = parser.parse_args()
    main(args)