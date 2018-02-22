from bottle import route, run
import requests
import lxml.html
import os
import re
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

  parameters = []
  header = ["step", "degree", "max#term", "Density", "total#term", "matsize"] * 4
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
      curves.append([[" "for _ in range(len(header)//4)] for __ in range(MAX_LENGTH)])
      row_num = 0
      curves[-1][row_num] = [c]+[ " " for _ in range(len(header)//4-1)]
      row_num += 1


    pickup("(Rank: \d+)",line, row)
    pickup("(Initial length: \d+)", line, row)

    if re.match("STEP \d+$",line)is not None or re.match("Total Faugere F4 time.+",line)is not None:
      for _ in range( len(header)//4 - len(row)):
        row.append(" ")
      curves[-1][row_num] = row
      row = []
      row_num += 1 

    pickup("(STEP \d+)$", line, row)
    pickup("Basis length.+step degree:\s(\d+),.+", line, row)
    pickup(".+ columns out of (\d+) .+", line, row)
    pickup("Density: (.+),.+", line, row)
    pickup("Density: .+, total: (\d+) .+", line, row)
    pickup("Matrix size: (\d+\sby\s\d+)", line, row)
    pickup("Approx mat (cost: [0-9./e/+]+),.+", line, output)

  # arrange
  data = [[] for _ in range(MAX_LENGTH)]
  for i in range(MAX_LENGTH):
    for curve in curves:
      data[i] += curve[i]

  output_rows.insert(0,parameters)
  output_rows += data


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

  spreadsheet_id = "16ifQsNMSNc9811B1LUh4ZSy25-o1ayI9YY7c7icDZ_g"

  values = output_rows
  # newsheet_title = datetime.datetime.today().strftime("%Y/%m/%d %H:%M:%S")
  newsheet_title = ' '.join(parameters[1:4])+" "+datetime.datetime.today().strftime("%H:%M:%S")
 # newsheet_title = "testtest"
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
  result = service.spreadsheets().values().batchUpdate(
  spreadsheetId=spreadsheet_id, body=body).execute()


  # with open("result.csv", 'w') as fout:
  #   csv.writer(fout).writerow(parameters)
  #   for row in output_rows:
  #     csv.writer(fout).writerow(row)

  return '''<meta http-equiv="refresh" content="3;URL=https://docs.google.com/spreadsheets/d/{spreadsheet_id}">
          <p>please wait...</p>
          <p><a href="https://docs.google.com/spreadsheets/d/' + spreadsheet_id + '">Click here</a>'''.format(spreadsheet_id=spreadsheet_id)
  
run(host='0.0.0.0', port=8900, debug=True)
