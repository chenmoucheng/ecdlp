from bottle import route, run
import requests
import lxml.html
import os
import re
import httplib2
from apiclient import discovery
from oauth2client.file import Storage

def str_isfloat(str):
    try:
        float(str)
        return True
    except ValueError:
        return False


def pickup(str, line, list):
    char = re.match(str, line)
    if ( char != None ):
        c = char.groups()[0]
        if str_isfloat(c):
            list.append(int(c)) if c.isdigit() else list.append(float(c))
        else: 
            list.append(c)

@route('/do/<URL:path>')
def do(URL):
    req = requests.get(URL)
    root = lxml.html.fromstring(req.text)
    
    output = []
    output_rows = [[], [], ["Step", "Deg", "#new", "time"]]
    precomp = True
    
    for line in root.text.split("\n"):
    
      if precomp:
        pickup("([A-z]\s=\s\d+)", line, output_rows[0])
        pickup("(T2\s=\s.+)", line, output_rows[0])
        pickup("(IX\s=\s.+)", line, output_rows[0])
        pickup("Loading(.+)", line, output_rows[0])
        if ( re.match("Weil.+", line) != None ):
          precomp = False
    
      else:
        pickup("STEP\s(\d+)", line, output)
        pickup("Basis length.+step degree:\s(\d+),.+", line, output)
        pickup("Num new poly.+:\s(\d+).+", line, output)
        if ( re.match("No new.+", line) != None ):
          output.append("no new")
        pickup("Step \d+ time:\s(\d+\.\d+)", line, output)
    
        if (len(output) == 4):
          output_rows.append(output)
          output = []
    
        if ( re.match("No pairs.+", line) != None ):
          output.append("No pairs")
          output.append("-")
          output_rows.append(output)
          output = []
    
        char = re.match("Gap.+:\s(\d+)\s.+", line)
        if (char != None ):
            output_rows[1].append("Last fall Degree = " + char.groups()[0])
    
        if (re.match("Point A 2",line) != None ):
            break;
    
    # print int(output_rows[-1][0])+2
    
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
    
    data = [
        {
            'range': "A:F",
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
    
    
    chart_title = "Transition"
    sourceSheetId = 0
    
    
    
    body = {
      "requests": [
        {
          "addChart": {
            "chart": {
              "spec": {
                "title": chart_title,
                "basicChart": {
                  "chartType": "COLUMN",
                  "legendPosition": "BOTTOM_LEGEND",
                  "axis": [
                    {
                      "position": "BOTTOM_AXIS",
                      "title": "Step"
                    }
                  ],
                  "domains": [
                    {
                      "domain": {
                        "sourceRange": {
                          "sources": [
                            {
                              "sheetId": sourceSheetId,
                              "startRowIndex": 2,
                              "endRowIndex": len(output_rows),
                              "startColumnIndex": 0,
                              "endColumnIndex": 1
                            }
                          ]
                        }
                      }
                    }
                  ],
                  "series": [
                    {
                      "series": {
                        "sourceRange": {
                          "sources": [
                            {
                              "sheetId": sourceSheetId,
                              "startRowIndex": 2,
                              "endRowIndex": len(output_rows),
                              "startColumnIndex": 1,
                              "endColumnIndex": 2
                            }
                          ]
                        }
                      },
                      "targetAxis": "LEFT_AXIS"
                    },
                    {
                      "series": {
                        "sourceRange": {
                          "sources": [
                            {
                              "sheetId": sourceSheetId,
                              "startRowIndex": 2,
                              "endRowIndex": len(output_rows),
                              "startColumnIndex": 2,
                              "endColumnIndex": 3
                            }
                          ]
                        }
                      },
                      "targetAxis": "LEFT_AXIS"
                    },
                    {
                      "series": {
                        "sourceRange": {
                          "sources": [
                            {
                              "sheetId": sourceSheetId,
                              "startRowIndex": 2,
                              "endRowIndex": len(output_rows),
                              "startColumnIndex": 3,
                              "endColumnIndex": 4
                            }
                          ]
                        }
                      },
                      "targetAxis": "LEFT_AXIS"
                    }
                  ],
                  "headerCount": 1
                }
              },
              "position": {
                "newSheet": True
              }
            }
          }
        }
      ]
    }
    
    response = service.spreadsheets().batchUpdate(spreadsheetId=spreadsheet_id,
                                                   body=body).execute()
    
    return '<p><a href="https://docs.google.com/spreadsheets/d/' + spreadsheet_id + '">Click here</a>'
    
    
    # with open("result.csv", "w") as fout:
    #     #writer = csv.writer(fout)
    #     csv.writer(fout).writerow(output_fileindex)
    #     csv.writer(fout).writerow(["Last fall Degree", last_D])
    #     for row in output_rows:
    #         csv.writer(fout).writerow(row)

run(host='0.0.0.0', port=8888, debug=True)

