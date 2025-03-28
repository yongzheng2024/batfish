import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# Set display options to show more rows and colums
pd.set_option('display.max_rows', None)  # Show all rows
pd.set_option('display.max_columns', None)  # Show all columns
pd.set_option('display.max_colwidth', None)  # Don't truncate column contents
# pd.set_option('display.expand_frame_repr', False) # Disable wrapping to multiple lines


# the directory of network topology and router configuration
SNAPSHOT_PATH = "../../networks/reachability_scenario1_true"

# Initialize a network and snapshot
NETWORK_NAME = "network-reachability-0001"
SNAPSHOT_NAME = "snapshot-reachability-0001"

bf = Session(host="localhost")
bf.set_network(NETWORK_NAME)

# when firstly execute this script, uncomment this line
bf.init_snapshot(SNAPSHOT_PATH, name=SNAPSHOT_NAME, overwrite=True)
# other scenarios, uncomment this line
# bf.set_snapshot(SNAPSHOT_PATH)

"""
# print related question list
questionLists = bf.q.list()
for question in questionLists:
    print(question)
"""

# forward path
# startNode = "as1border2"
# endNode = "as2border1"  # reachable
# endNode = "as2core1"    # non-reachable
# endNode = "as3border1"

# reserve path
startNode = "as2border1"
# endNode = "as1border1"
endNode = "as1core1"

reachablePathConstraints = PathConstraints(startLocation=startNode, endLocation=endNode)

# Verify reachability about entire network
# result = bf.q.reachability().answer().frame()
result = bf.q.reachability(pathConstraints=reachablePathConstraints).answer().frame()

# Pretty print the result
print(result)
