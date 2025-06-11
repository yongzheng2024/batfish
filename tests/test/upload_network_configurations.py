import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# the directory of network topology and router configuration
SNAPSHOT_PATH_1 = "../../networks/lightyear_example"
SNAPSHOT_PATH_2 = "../../networks/lightyear_example_bgp"
SNAPSHOT_PATH_11 = "../../networks/test_example"

NETWORK_NAME_1 = "network-example-0011"

SNAPSHOT_NAME_1 = "snapshot-lightyear-example-0001"
SNAPSHOT_NAME_2 = "snapshot-lightyear-example-0002"
SNAPSHOT_NAME_11 = "snapshot-test-example-0012"

# Initialize a network and snapshot

# when firstly execute this script, uncomment this line
# bf.init_snapshot(SNAPSHOT_PATH, name=SNAPSHOT_NAME, overwrite=True)
# other scenarios, uncomment this line
# bf.set_snapshot(SNAPSHOT_PATH)

bf1 = Session(host="localhost")
bf1.set_network(NETWORK_NAME_1)
bf1.init_snapshot(SNAPSHOT_PATH_1, name=SNAPSHOT_NAME_1, overwrite=True)
bf1.init_snapshot(SNAPSHOT_PATH_2, name=SNAPSHOT_NAME_2, overwrite=True)
bf1.init_snapshot(SNAPSHOT_PATH_11, name=SNAPSHOT_NAME_11, overwrite=True)
