import random
import numpy as np
import pandas as pd

# our objective function
def objective_function(x):
    return -(x[1] + 47) * np.sin(np.sqrt(np.abs(x[0] / 2 + (x[1] + 47)))) - x[
        0
    ] * np.sin(np.sqrt(np.abs(x[0] - (x[1] + 47))))


def rhc(sp, p, z, seed):
    random.seed(seed)
    curr_best = [1, sp, objective_function(sp)]
    return rhc2(sp, p, z, curr_best)


def rhc2(sp, p, z, curr_best):  # returns [#solSearched, sol, f(sol)]
    old_best = curr_best
    sample_list = []
    # sample generation
    for i in range(p):
        z1, z2 = random.uniform(-z, z), random.uniform(-z, z)
        neighbor = [sp[0] + z1, sp[1] + z2]
        if neighbor[0] < -512:
            neighbor[0] = -512
        if neighbor[0] > 512:
            neighbor[0] = 512
        if neighbor[1] < -512:
            neighbor[1] = -512
        if neighbor[1] > 512:
            neighbor[1] = 512
        sample_list.append(neighbor)

    # look through sample
    for point in sample_list:
        # evaluating sample
        f_point = objective_function(point)
        curr_best[0] += 1
        if f_point < curr_best[2]:
            curr_best = [curr_best[0], point, f_point]

    if old_best == curr_best:  # terminate condition
        return old_best
    return rhc2(curr_best[1], p, z, curr_best)


# starting variables
# [[404,504],[0,0.23],[-200,300],[412,-99.9]]
# [3,0.5]
# [30,250]
sp = [404, 504]
# sp = [0,0.23]
# sp = [-200,300]
# sp = [412,-99.9]
# sp=[512,400]

z = 350
p = 250

[starting_point, lowest_point, lowest_val] = rhc(sp=sp, p=p, z=z, seed=100)
print("The Mininum: ")
print(">%d f(%s) = %.5f" % (starting_point, lowest_point, lowest_val))

