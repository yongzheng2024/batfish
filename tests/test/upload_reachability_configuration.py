import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# the directory of network topology and router configuration
SNAPSHOT_PATH_1 = "../../networks/reachability_scenario1/true_without_acl"
SNAPSHOT_PATH_2 = "../../networks/reachability_scenario1/false_without_acl"
SNAPSHOT_PATH_3 = "../../networks/reachability_scenario1/true_with_acl"
SNAPSHOT_PATH_4 = "../../networks/reachability_scenario1/false_with_acl"
"""
SNAPSHOT_PATH_5 = "../../networks/reachability_scenario2/true_without_acl"
SNAPSHOT_PATH_6 = "../../networks/reachability_scenario2/false_without_acl"
"""

# Initialize a network and snapshot
NETWORK_NAME = "network-reachability-scenario1"
SNAPSHOT_NAME_1 = "snapshot-reachability-0001"
SNAPSHOT_NAME_2 = "snapshot-reachability-0002"
SNAPSHOT_NAME_3 = "snapshot-reachability-0003"
SNAPSHOT_NAME_4 = "snapshot-reachability-0004"
"""
NETWORK_NAME = "network-reachability-scenario2"
SNAPSHOT_NAME_5 = "snapshot-reachability-0001"
SNAPSHOT_NAME_6 = "snapshot-reachability-0002"
"""

bf = Session(host="localhost")
bf.set_network(NETWORK_NAME)

# when firstly execute this script, uncomment this line
# bf.init_snapshot(SNAPSHOT_PATH, name=SNAPSHOT_NAME, overwrite=True)
# other scenarios, uncomment this line
# bf.set_snapshot(SNAPSHOT_PATH)

bf.init_snapshot(SNAPSHOT_PATH_1, name=SNAPSHOT_NAME_1, overwrite=True)
bf.init_snapshot(SNAPSHOT_PATH_2, name=SNAPSHOT_NAME_2, overwrite=True)
bf.init_snapshot(SNAPSHOT_PATH_3, name=SNAPSHOT_NAME_3, overwrite=True)
bf.init_snapshot(SNAPSHOT_PATH_4, name=SNAPSHOT_NAME_4, overwrite=True)
"""
bf.init_snapshot(SNAPSHOT_PATH_5, name=SNAPSHOT_NAME_5, overwrite=True)
bf.init_snapshot(SNAPSHOT_PATH_6, name=SNAPSHOT_NAME_6, overwrite=True)
"""
