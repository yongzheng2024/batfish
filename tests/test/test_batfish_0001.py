import pandas as pd
from pybatfish.client.session import Session
from pybatfish.datamodel import *
from pybatfish.datamodel.answer import *
from pybatfish.datamodel.flow import *

# the directory of network topology and router configuration
SNAPSHOT_PATH = '../../networks/example/live'

# Initialize a network and snapshot
NETWORK_NAME = 'network-test-batfish-0001'
SNAPSHOT_NAME = 'snapshot-test-batfish-0001'

bf = Session(host="localhost")
bf.set_network(NETWORK_NAME)

# when firstly execute this script, uncomment this line
bf.init_snapshot(SNAPSHOT_PATH, name=SNAPSHOT_NAME, overwrite=True)
# other scenarios, uncomment this line
# bf.set_snapshot(SNAPSHOT_NAME)

nodes = bf.q.nodeProperties().answer().frame()
print("nodes = bf.q.nodeProperties().answer().frame()")
print(nodes)
print()
print(nodes.iloc[0])
print()

interface = bf.q.interfaceProperties().answer().frame()
print("interface = bf.q.interfaceProperties().answer().frame()")
print(interface)
print()
print(interface.iloc[0])
print()

# ip = bf.q.ipOwners().answer().frame()
# print("ip = bf.q.ipOwners().answer().frame()")
# print(ip)
# print()
# print(ip.iloc[0])
# print()
# 
# bgp = bf.q.bgpProcessConfiguration().answer().frame()
# print("bgp = bf.q.bgpProcessConfiguration().answer().frame()")
# print(bgp)
# print()
# print(bgp.iloc[0])
# print()
# 
# bgpPeer = bf.q.bgpPeerConfiguration().answer().frame()
# print("bgpPeer = bf.q.bgpPeerConfiguration().answer().frame()")
# print(bgpPeer)
# print()
# print(bgpPeer.iloc[0])
# print()
# print(bgpPeer.iloc[1])
# print()
# print(bgpPeer.iloc[2])
# print()
# print(bgpPeer.iloc[3])
# print()
# 
# result = bf.q.testRoutePolicies(policies='/as1_to_/', direction='in', inputRoutes=list([BgpRoute(network='10.0.0.0/24', originatorIp='4.4.4.4', originType='egp', protocol='bgp', asPath=[[64512, 64513], [64514]], communities=['64512:42', '64513:21'])])).answer().frame()
# print(result)
# print()
# print(result.iloc[0])
# print()
