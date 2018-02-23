from bottle import route, run
import requests
import lxml.html
import os
import re
import httplib2
from apiclient import discovery
from oauth2client.file import Storage
import datetime

def str_isfloat(s):
  try:
    float(s)
    return True
  except ValueError:
    return False

def pickup(s, line, l):
  char = re.match(s, line)
  if char is not None:
    c = char.groups()[0]
    if str_isfloat(c):
      l.append(int(c)) if c.isdigit() else l.append(float(c))
    else: 
      l.append(c)

def write_spreadsheet(sheetid, title, row_major_data):
  spreadsheet_id = sheetid
  newsheet_title = title
  values = row_major_data

  home_dir = os.path.expanduser('~')
  credential_dir = os.path.join(home_dir, '.credentials')
  credential_filename = 'sheets.googleapis.com-python-fromLogtoSheet.json'
  credential_path = os.path.join(credential_dir,credential_filename)
  credentials = Storage(credential_path).get()
  http = credentials.authorize(httplib2.Http())
  discoveryUrl = ('https://sheets.googleapis.com/$discovery/rest?''version=v4')
  service = discovery.build('sheets', 'v4', http=http,discoveryServiceUrl=discoveryUrl)

  # newsheet_title = datetime.datetime.today().strftime("%Y/%m/%d %H:%M:%S")

  create_sheet_body = {
    "requests": [
      {
      "addSheet": {
        "properties": {
          "title": newsheet_title
          }
        }
      }
    ]
  }  

  request = service.spreadsheets().batchUpdate(spreadsheetId=spreadsheet_id, body=create_sheet_body)
  response = request.execute()
  newsheetId = response["replies"][0]["addSheet"]["properties"]["sheetId"]

  newsheetrange = newsheet_title + "!A:ZZ"
  data = [
  {
    'range': newsheetrange,
    'values': values
  }
  # Additional ranges to update ...
  ]
  body = {
    'valueInputOption': "RAW",
    'data': data
  }
  result = service.spreadsheets().values().batchUpdate(spreadsheetId=spreadsheet_id, body=body).execute()


@route('/do/<URL:path>')
def do(URL):
  URL =  "http://133.1.144.141:8080/"+URL
  req = requests.get(URL)
  root = lxml.html.fromstring(req.text)

  D = []
  gap = []
  output = []
  parameters = []
  header = ["Curve", "Matcost", "Time", "Dreg", "Gap", "Rank"]*5
  output_rows = []
  core = False
  rank_bl = False
  output_rows.append([URL])
  output_rows.append(header)

  for line in root.text.split("\n"):
  #for line in open("input.txt", 'r'):
    pickup("([A-z]([A-z0-9])?\s=\s.+)", line, parameters)

    pickup("Working on (\S+) Elliptic.+", line, output)

    # append output list for each set (experiment for 4 curves) finishing.
    if re.match("Finished Point .+",line) is not None:
      output_rows.append(output) 
      output = []

    # ignore f4 logs for rewriting variables 
    if re.match("Rewriting variables", line) is not None:
      core = False

    # sign of starting core f4.
    if re.match("Computing core variety...",line) is not None:
      core = True

    # pick up from core f4 logs  
    if core:
      pickup("Basis length.+step degree:\s(\d+),.+", line, D)
      if re.match("No pairs.+", line) is not None: 
        D.pop()
      pickup("Approx mat cost: ([0-9./e/+]+),.+", line, output)
      # consider only first one
      if re.match("Total Faugere F4 time.+",line)is not None:
        pickup("Total Faugere.+:\s(\d+\.\d+),.+", line, output)
        output.append(max(D))
        D = []  
        core = False

    pickup(".+Gap degree.+ (\d+) .+=.+", line, gap)
    if re.match("Rank of relation.+",line)is not None:
      rank_bl = True
      output.append(','.join(map(str,gap)))
      gap = []
      pickup("Rank of relation matrix: (\d+)", line, output)

    if re.match("Point B+.",line)is not None and not rank_bl:
      output.append(','.join(map(str,gap)))
      gap = []
      output.append('no rank')

  output_rows.insert(0,parameters)

  sheetid = "1opFSZCBUryQBTF2JrmRGKubJdd_j2aeAAPYQzWMb-Ys"
  title = ' '.join(parameters[1:4])+" "+datetime.datetime.today().strftime("%H:%M:%S")
  write_spreadsheet(sheetid, title, output_rows)

  return '''<meta http-equiv="refresh" content="3;URL=https://docs.google.com/spreadsheets/d/{sheetid}">
          <p>please wait...</p>
          <p><a href="https://docs.google.com/spreadsheets/d/' + spreadsheet_id + '">Click here</a>'''.format(sheetid=sheetid)
  


@route('/detail/<URL:path>')
def detail(URL):
  URL =  "http://133.1.144.141:8080/"+URL
  req = requests.get(URL)
  root = lxml.html.fromstring(req.text)

  parameters = []
  header = ["degree", "max#term", "Density", "total#term", "matsize", "time"] * 4
  output_rows = []
  output_rows.append([URL])
  output_rows.append(header)
  curves = []
  MAX_LENGTH = 500
  row = []

  for line in root.text.split("\n"):
  # for line in open("test.txt", 'r'):
    pickup("([A-z]([A-z0-9])?\s=\s.+)", line, parameters)

    char = re.match("Working on (\S+) Elliptic.+", line)
    if char is not None:
      c = char.groups()[0]
      curves.append([[""for _ in range(len(header)//4)] for __ in range(MAX_LENGTH)])
      row_num = 0
      curves[-1][row_num] = [c]+[ "" for _ in range(len(header)//4-1)]
      row_num += 1

    pickup("(Rank: \d+)",line, row)
    pickup("(Initial length: \d+)", line, row)

    if re.match("STEP \d+$",line)is not None or \
       re.match("^Reduce .+",line)is not None or \
       re.match("Total Faugere F4 time.+",line)is not None:
      for _ in range( len(header)//4 - len(row)):
        row.append("")
      curves[-1][row_num] = row
      row = []
      row_num += 1 

    # pickup("(STEP \d+)$", line, row)
    pickup("Basis length.+step degree:\s(\d+),.+", line, row)
    pickup(".+ columns out of (\d+) .+", line, row)
    pickup("Density: (.+),.+", line, row)
    pickup("Density: .+, total: (\d+) .+", line, row)
    pickup("Matrix size: (\d+\sby\s\d+)", line, row)
    pickup("Approx mat (cost: [0-9./e/+]+),.+", line, row)
    pickup("Step \d+ time: (\d+\.\d+),.+", line ,row)

  # arrange
  data = [[] for _ in range(MAX_LENGTH)]
  for i in range(MAX_LENGTH):
    for curve in curves:
      data[i] += curve[i]

  output_rows.insert(0,parameters)
  output_rows += data

  sheetid = "16ifQsNMSNc9811B1LUh4ZSy25-o1ayI9YY7c7icDZ_g"
  title = ' '.join(parameters[1:4])+" "+datetime.datetime.today().strftime("%H:%M:%S")
  write_spreadsheet(sheetid, title, output_rows)

  return '''<meta http-equiv="refresh" content="3;URL=https://docs.google.com/spreadsheets/d/{sheetid}">
          <p>please wait...</p>
          <p><a href="https://docs.google.com/spreadsheets/d/' + spreadsheet_id + '">Click here</a>'''.format(sheetid=sheetid)
 

run(host='0.0.0.0', port=8888, debug=True)

