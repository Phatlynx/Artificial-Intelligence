# This file is to create heatmaps
from matplotlib import pyplot as plt
from matplotlib.tri import Triangulation
import numpy as np
from q_learning import *


def triangulation_for_triheatmap(M, N):
    xv, yv = np.meshgrid(np.arange(-0.5, M), np.arange(-0.5, N))  # vertices of the little squares
    xc, yc = np.meshgrid(np.arange(0, M), np.arange(0, N))  # centers of the little squares
    x = np.concatenate([xv.ravel(), xc.ravel()])
    y = np.concatenate([yv.ravel(), yc.ravel()])
    cstart = (M + 1) * (N + 1)  # indices of the centers

    trianglesN = [(i + j * (M + 1), i + 1 + j * (M + 1), cstart + i + j * M)
                  for j in range(N) for i in range(M)]
    trianglesE = [(i + 1 + j * (M + 1), i + 1 + (j + 1) * (M + 1), cstart + i + j * M)
                  for j in range(N) for i in range(M)]
    trianglesS = [(i + 1 + (j + 1) * (M + 1), i + (j + 1) * (M + 1), cstart + i + j * M)
                  for j in range(N) for i in range(M)]
    trianglesW = [(i + (j + 1) * (M + 1), i + j * (M + 1), cstart + i + j * M)
                  for j in range(N) for i in range(M)]
    return [Triangulation(x, y, triangles) for triangles in [trianglesN, trianglesE, trianglesS, trianglesW]]



exp = experiment(2, seed=577)

male = 0
#situation = 'a'
#situation = 'b'
situation = 'c'




M, N = 5, 5
print(f"\nFirst filled dropoff location = {exp.firstFilledDropOffLocation}")
if situation == 'a':
    print(f"Situation a encountered at step {exp.situation_a_step}")
    values = exp.converted_qTables_situation_a[male]
    femalePos, malePos = exp.situation_a_agentPositions
    femaleHolding, maleHolding = exp.situation_a_agentHoldings
    print(f"pickup index status is {exp.situation_a_pickUpIndexStatus}")
if situation == 'b':
    print(f"Situation b encountered at step {exp.situation_b_step}")
    values = exp.converted_qTables_situation_b[male]
    femalePos, malePos = exp.situation_b_agentPositions
    femaleHolding, maleHolding = exp.situation_b_agentHoldings
if situation == 'c':
    values = exp.converted_qTables_situation_c[male]
    femalePos, malePos = exp.situation_c_agentPositions
    femaleHolding, maleHolding = exp.situation_c_agentHoldings
    print(f"pickup index status is {exp.situation_c_pickUpIndexStatus}")
    print(f"dropoff index status is {exp.situation_c_dropOffIndexStatus}")
vmin_ = np.min(values)
vmax_ = np.max(values)
triangul = triangulation_for_triheatmap(M, N)
fig, ax = plt.subplots()
imgs = [ax.tripcolor(t, val.ravel(), cmap='RdYlGn', vmin=-1, vmax=1, ec='white') for t, val in zip(triangul, values)]
for val, dir in zip(values, [(-1, 0), (0, 1), (1, 0), (0, -1)]):
    for i in range(M):
        for j in range(N):
            v = val[j, i]
            ax.text(i + 0.31 * dir[1], j + 0.31 * dir[0], f'{v:.2f}', color='k', ha='center', va='center')
cbar = fig.colorbar(imgs[1], ax=ax)

ax.set_xticks(range(M))
ax.set_yticks(range(N))
ax.invert_yaxis()
ax.margins(x=0, y=0)
ax.set_aspect('equal', 'box')  # square cells
ax.set_title(f"Male is {'holding' if maleHolding else 'not holding'} at {malePos}") if male else ax.set_title(f"Female is {'holding' if femaleHolding else 'not holding'} at {femalePos}")
plt.tight_layout()
plt.show()