import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.route import BgpRoute
from pybatfish.datamodel.route import BgpRouteConstraints
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# the directory of network topology and router configuration
SNAPSHOT_PATH = "../../networks/simple-routing-policies"

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

# Verify reachability about entire network
result = bf.q.reachability().answer().frame()

# Pretty print the result
print(result)
