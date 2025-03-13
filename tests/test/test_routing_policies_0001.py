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
NETWORK_NAME = "network-routing-policies-0001"
SNAPSHOT_NAME = "snapshot-routing-policies-0001"

bf = Session(host="localhost")
bf.set_network(NETWORK_NAME)

# when firstly execute this script, uncomment this line
bf.init_snapshot(SNAPSHOT_PATH, name=SNAPSHOT_NAME, overwrite=True)
# other scenarios, uncomment this line
# bf.set_snapshot(SNAPSHOT_PATH)

# questionLists = bf.q.list()
# for question in questionLists:
#     print(question)

# Define the space of private addresses
privateIps = ["10.0.0.0/8:8-32", 
              "172.16.0.0/12:12-32", 
              "192.168.0.0/16:16-32"]

# Specify all route announcements for the private space
inRoutes = BgpRouteConstraints(prefix=privateIps)

# Verify that no such announcement is permitted by our policy
result = bf.q.searchRoutePolicies(policies="from_customer", 
                                  inputConstraints=inRoutes,
                                  action="permit").answer().frame()

# Pretty print the result
print(result)
