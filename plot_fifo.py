#!/bin/python

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
import csv
import sys

x_man = []
y_man = []
x_gem = []
y_gem = []
x_i1 = []
y_i1 = []
x_gpt = []
y_gpt = []

with open("./reports/fifo_manual.csv", mode='r') as f:
    csv_reader = csv.DictReader(f)
    for row in csv_reader:
        x_man.append(float(row["Elements"]))
        y_man.append(float(row["Time"]))

with open("./reports/fifo_gemini.csv", mode='r') as f:
    csv_reader = csv.DictReader(f)
    for row in csv_reader:
        x_gem.append(float(row["Elements"]))
        y_gem.append(float(row["Time"]))

with open("./reports/fifo_manual_int1.csv", mode='r') as f:
    csv_reader = csv.DictReader(f)
    for row in csv_reader:
        x_i1.append(float(row["Elements"]))
        y_i1.append(float(row["Time"]))

with open("./reports/fifo_gpt.csv", mode='r') as f:
    csv_reader = csv.DictReader(f)
    for row in csv_reader:
        x_gpt.append(float(row["Elements"]))
        y_gpt.append(float(row["Time"]))

fig, ax = plt.subplots(figsize=(7,6))

ax.plot(x_i1, y_i1, label = "Manual (Int Width = 1)")
ax.plot(x_man, y_man, label = "Manual (Int Width = 5)")
ax.plot(x_gem, y_gem, label = "Gemini")
#ax.plot(x_gpt, y_gpt, label = "GPT", marker = 'x')

ax.set_xlabel('Elements')
ax.set_ylabel('Solution Time')
ax.set_title('Fifo Runtimes')
ax.legend()

plt.show()

