import glob
import re
import numpy as np
from scipy import stats
import csv

with open("result.csv", "w") as fout:
    #writer = csv.writer(fout)
    list = ["l", "m", "n", "q", "Dreg", "T_inter", "T_GB", "Q1", "Q3", "Order"]
    csv.writer(fout).writerow(list)


for file in glob.glob("./work/*.txt"):
    print file
    D = []
    Dreg = []
    Tinter = []
    TGB = []
    case = False

    for line in open(file,"r"):
        char = re.match("[A-z]\s=\s(\d+)", line)
        if ( char != None ):
            with open("result.csv", "a") as fout:
                fout.writelines(char.groups())
                fout.write(",")

        if ( re.match("Weil.+", line) != None ): case = True
        if ( re.match("Point\s.+", line) != None ):
            case = False
            if (len(D) != 0):
                Dreg.append(max(D))
                D = []

        char = re.search("step degree:\s(\d+),.+", line)
        if ( char != None ) and case:
            D.append(int(char.groups()[0]))

        if (re.search("No pairs.+", line) != None) and case: D.pop()

        char = re.search("Total Faugere.+:\s(\d+\.\d+),.+", line)
        if ( char != None ):
            if (case): TGB.append(float(char.groups()[0]))
            else : Tinter.append(float(char.groups()[0]))

        char = re.match("Order:\s(\d+)", line)
        if ( char != None ): order = long(char.groups()[0])

    with open("result.csv", "a") as fout:
        list = [str(np.mean(Dreg)), str(np.mean(Tinter)), str(np.mean(TGB)), \
                str(stats.scoreatpercentile(TGB, 25)),  \
                str(stats.scoreatpercentile(TGB, 75)), str(order) ]
        csv.writer(fout).writerow(list)
