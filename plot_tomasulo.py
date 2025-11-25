#!/bin/python

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
import csv
import sys

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

fig = plt.figure()
ax = fig.add_subplot()
ax.scatter(x, y)

ax.set_xlabel('Number of Registers and ROB Entries')
ax.set_ylabel('Number of Steps')
ax.set_title('Tomasulos ' + sys.argv[1] + ' Runtimes')

plt.show()


