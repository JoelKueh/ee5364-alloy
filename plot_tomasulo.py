#!/bin/python

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
import numpy as np
import csv
import sys
import subprocess

fnames=[
    "./reports/tomasulo_NoWARHazard_Complete.csv",
    "./reports/tomasulo_NoWAWHazard_Complete.csv",
    "./reports/tomasulo_NoWARHazard_WARVulnerable.csv",
    "./reports/tomasulo_NoWAWHazard_WAWVulnerable.csv"
]

plotnames=[
    "NoWARHazard_Complete",
    "NoWAWHazard_Complete",
    "NoWARHazard_WARVulnerable",
    "NoWAWHazard_WAWVulnerable"
]

if len(sys.argv) == 1:
    for i in range(0, len(fnames)):
        subprocess.run(["./plot_tomasulo.py", plotnames[i], fnames[i]])
    exit()

fname=sys.argv[2]

x = []
y = []
z = []
with open(fname, mode='r') as f:
    csv_reader = csv.DictReader(f)
    for row in csv_reader:
        x.append(row["RegsAndEntries"])
        y.append(row["Steps"])
        z.append(row["Time"])
z = [float(val)/1000 for val in z]

fig, ax = plt.subplots(figsize=(7,6))

ax.set_xlabel('Number of Registers and ROB Entries')
ax.set_ylabel('Number of Steps')
ax.set_title('Tomasulos ' + sys.argv[1] + ' Runtimes')

sc = ax.scatter(x, y, s=20, c=z, marker = 'o', cmap = cm.jet)

cbar = plt.colorbar(sc, ax=ax)
cbar.set_label("Solution Times (seconds)")

plt.show()

