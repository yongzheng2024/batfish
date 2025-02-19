import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.route import BgpRouteConstraints
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# the directory of network topology and router configuration
SNAPSHOT_PATH = "./0_routing_policies_configs"

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

# singlePrivateIps = ["10.0.0.0/11:11-11"]      # accepted
# singlePrivateIps = ["192.168.0.0/17:17-17"]   # error
# singlePrivateIps = ["11.0.0.0/11:11-11"]      # error

# Specify all route announcements for the private space
inRoutes1 = BgpRouteConstraints(prefix=privateIps)
# inRoutes2 = BgpRouteConstraints(prefix=singlePrivateIps)

# Verify that no such announcement is permitted by our policy
result = bf.q.searchRoutePolicies(policies="from_customer", 
                                  inputConstraints=inRoutes1, 
                                  action="permit").answer().frame()

# Pretty print the result
print(result)
