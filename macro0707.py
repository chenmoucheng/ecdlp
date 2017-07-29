from bottle import route, run
import requests
import lxml.html
import os
import re
import csv
import httplib2
from apiclient import discovery
from oauth2client.file import Storage
import datetime

def str_isfloat(str):
  try:
    float(str)
    return True
  except ValueError:
    return False

def pickup(str, line, list):
  char = re.match(str, line)
  if char is not None:
    c = char.groups()[0]
    if str_isfloat(c):
      list.append(int(c)) if c.isdigit() else list.append(float(c))
    else: 
      list.append(c)


@route('/do/<URL:path>')
def do(URL):
  URL =  "http://133.1.144.141:8080/"+URL
  req = requests.get(URL)
  root = lxml.html.fromstring(req.text)

  D = []
  gap = []
  output = []
  parameters = []
  header = ["Curve", "Matcost", "Time", "Dreg", "Gap", "Rank",
            "Curve", "Matcost", "Time", "Dreg", "Gap", "Rank",
            "Curve", "Matcost", "Time", "Dreg", "Gap", "Rank",
            "Curve", "Matcost", "Time", "Dreg", "Gap", "Rank"]
  output_rows = []
  core = False
  output_rows.append(header)


  for line in root.text.split("\n"):
  #for line in open("input.txt", 'r'):
    pickup("([A-z]([A-z0-9])?\s=\s.+)", line, parameters)

    pickup("Working on ([A-z]+) Elliptic.+", line, output)

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

    pickup("\s\sGap degree.+ (\d+) .+=.+", line, gap)
    if re.match("Rank of relation.+",line)is not None:
      output.append(','.join(map(str,gap)))
      gap = []
      pickup("Rank of relation matrix: (\d+)", line, output)


  output_rows.insert(0,parameters)


  home_dir = os.path.expanduser('~')
  credential_dir = os.path.join(home_dir, '.credentials')
  credential_filename = 'sheets.googleapis.com-python-fromLogtoSheet.json'
  credential_path = os.path.join(credential_dir,credential_filename)
  credentials = Storage(credential_path).get()
  http = credentials.authorize(httplib2.Http())
  discoveryUrl = ('https://sheets.googleapis.com/$discovery/rest?'
                  'version=v4')
  service = discovery.build('sheets', 'v4', http=http,
                            discoveryServiceUrl=discoveryUrl)

  spreadsheet_id = "1opFSZCBUryQBTF2JrmRGKubJdd_j2aeAAPYQzWMb-Ys"

  values = output_rows
  #newsheet_title = datetime.datetime.today().strftime("%Y/%m/%d %H:%M:%S")
  newsheet_title = ' '.join(parameters[1:4])

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

  newsheetrange = newsheet_title + "!A:X"
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
  result = service.spreadsheets().values().batchUpdate(
  spreadsheetId=spreadsheet_id, body=body).execute()


  # with open("result.csv", 'w') as fout:
  #   csv.writer(fout).writerow(parameters)
  #   for row in output_rows:
  #     csv.writer(fout).writerow(row)

  return '''<meta http-equiv="refresh" content="3;URL=https://docs.google.com/spreadsheets/d/{spreadsheet_id}">
          <p>please wait...</p>
          <p><a href="https://docs.google.com/spreadsheets/d/' + spreadsheet_id + '">Click here</a>'''.format(spreadsheet_id=spreadsheet_id)
  
run(host='0.0.0.0', port=8888, debug=True)
