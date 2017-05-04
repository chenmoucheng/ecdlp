import os.path
import glob
import re
import numpy as np
from scipy import stats
import csv


print "please input directory name:"
foldername = raw_input()

if not os.path.isdir("./" + foldername): print "Directory is not found"

for file in glob.glob( "./" + foldername + "/*.txt"):
    print file
    output_fileindex = []
    output = []
    output_rows = [["Step", "Deg", "#new", "time"]]
    precomp = True
    last_D = 0;

    for line in open(file,"r"):
        char = re.match("([A-z]\s=\s\d+)", line)
        if ( char != None ):
            output_fileindex.append(char.groups()[0])

        char = re.search("(T2\s=\s.+)", line)
        if ( char != None ):
            output_fileindex.append(char.groups()[0])

        char = re.search("(IX\s=\s.+)", line)
        if ( char != None ):
            output_fileindex.append(char.groups()[0])

        if ( re.match("Weil.+", line) != None ):
            precomp = False

        if not precomp:
	        char = re.search("STEP\s(\d+)", line)
	        if ( char != None ):
	            if (len(output) != 0):
	                output_rows.append(output)
	                output = []
	            output.append(char.groups()[0])

	        char = re.search("step degree:\s(\d+),.+", line)
	        if ( char != None ):
	            output.append(char.groups()[0])

	        char = re.search("Num new poly.+:\s(\d+).+", line)
	        if ( char != None ):
	            output.append(char.groups()[0])

	        if ( re.search("No new.+", line) != None ):
	            output.append("no new")

	        char = re.search("No pairs.+", line)
	        if ( re.search("No pairs.+", line) != None ):
	            output.append("No pairs")

	        char = re.search("Step \d+ time:\s(\d+\.\d+)", line)
	        if ( char != None ):
	            output.append(char.groups()[0])

	        if ( re.search("Final basis length.+", line) != None):
	            output_rows.append(output)
	            output = []

        char = re.search("Gap.+:\s(\d+)\s.+", line)
        if (char != None ):
            last_D = char.groups()[0]

    with open("result.csv", "w") as fout:
        #writer = csv.writer(fout)
        csv.writer(fout).writerow(output_fileindex)
        csv.writer(fout).writerow(["Last fall Degree", last_D])
        for row in output_rows:
            csv.writer(fout).writerow(row)
