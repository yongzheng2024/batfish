### <b>Configure Batfish and Pybatfish</b>

#### Configure Batfish on Ubuntu (non-Docker)

> [configure batfish on other platform that can refer building and running Batfish document](https://github.com/batfish/batfish/tree/master/docs/building_and_running)

```sh
# install dependencies (java11, bazel)
$ sudo apt install openjdk-11-jdk openjdk-11-dbg
$ sudo apt install wget
$ wget -O- https://github.com/bazelbuild/bazelisk/releases/download/v1.12.2/bazelisk-linux-amd64 | sudo tee /usr/local/bin/bazelisk > /dev/null
$ sudo chmod +x /usr/local/bin/bazelisk
$ sudo ln -s bazelisk /usr/local/bin/bazel

# git clone batfish/batfish with tags (v2024.07.10)
# git clone --branch v2024.07.10 https://github.com/batfish/batfish.git

# git clone yongzheng2024/batfish with branch feature-v2024
$ git clone --branch feature-v2024 https://github.com/yongzheng2024/batfish.git

# build and run batfish
$ cd /PATH-TO/batfish
$ ./tool/bazel_run.sh

# batfish server running ...

# run test (optional)
bazel test //...
```

#### Configure PyBatfish on Ubuntu (non-Docker)

> [PyBatfish usage document](https://pybatfish.readthedocs.io/en/latest/getting_started.html) <br>
> [PyBatfish interact with the Batfish service](https://pybatfish.readthedocs.io/en/latest/notebooks/interacting.html#)

```sh
# install pybatfish
$ python3 -m pip install --upgrade pybatfish

# interact with the batfish service
# make sure the batfish service running

# create test cases directory
$ cd /PATH-TO/batfish
$ cd tests
$ mkdir test  # you can modify the directory name

# create test case script
$ cd test
$ touch test_batfish_0001.py

# you can interact with the running batfish service
$ cat test_batfish_0001.py
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
```

#### Use Batfish and PyBatfish on Ubuntu (non-Docker)

> [IntelliJ IDEA configuration document](https://github.com/batfish/batfish/tree/master/docs/intellij_setup)

```sh
# configure the IntelliJ IDEA process as follows:
# firstly, install plugins `Bazel For IntelliJ` and `Bazel (EAP)`
# secondly, file - import bazel project - create from scratch
# finally, edit Run/Debug Configurations - add bazel command
#
# * Target expression (Java_binary handled by Java Handler)
#   + //projects/allinone:allinone_main
# * Bazel command
#   + run
# * Bazel flags
#   + --jvmopt=-Xmx12g
#   + --jvmopt=-Dlog4j2.configurationFile=tools/log4j2.yaml
#   + --java_runtime_version=11
#   + --run_under="cd /PATH-TO/batfish &&"
# * Executable flags
#   + -runclient
#   + false
#   + -coordinatorargs
#   + "-templatedirs ./questions"
# note: please remove "#" and "+" char
#       and modify `/PATH-TO/batfish` to your batfish directory

# open a terminal to build and run batfish service
$ cd /PATH-TO/batfish
$ tools/bazel_run.sh
# or open batfish in IntelliJ IDEA
# run //projects/allinone:allinone_main

# open another terminal to execute batfish query via pybatfish
$ cd /PATH-TO/batfish/tests/test
$ python3 test_batfish_0001.py
nodes = bf.q.nodeProperties().answer().frame()
          Node AS_Path_Access_Lists  ...         VRFs Zones
0   as2border2                   []  ...  ['default']    []
1   as1border1                   []  ...  ['default']    []
2   as3border2                   []  ...  ['default']    []
3   as1border2                   []  ...  ['default']    []
4     as2dept1                   []  ...  ['default']    []
5     as2dist2                   []  ...  ['default']    []
6     as3core1                   []  ...  ['default']    []
7     as2core1                   []  ...  ['default']    []
8     as1core1                   []  ...  ['default']    []
9        host1                   []  ...  ['default']    []
10       host2                   []  ...  ['default']    []
11  as3border1                   []  ...  ['default']    []
12    as2core2                   []  ...  ['default']    []
13    as2dist1                   []  ...  ['default']    []
14  as2border1                   []  ...  ['default']    []

[15 rows x 37 columns]

omitting ...

# you can check network and snapshot via URL
# http://localhost:9996/v2/networks
```

### Directory Structure

#### Partial Directory Structure via Tree Command

```txt
Batfish
├── bdds                 ### output directory (order from 0000 to 9999), invlving bdd
│   │                    ### encoding, smt encoding and link between configs and smt variables
│   ├── README.md        ### README file about output
│   └── routing_policies_0000
│       ├── border1   <----------------------------------------------+
│       │   ├── bdd_encoding                                         |
│       │   ├── link_configuration   <-------------------------------+ 
│       │   └── smt_encoding                                         |
│       └── border2   <----------------------------------------------|---+
│           ├── bdd_encoding                                         |   |
│           ├── link_configuration   <-------------------------------|---+
│           └── smt_encoding                                         |   |
├── docs                 ### documents                               |   |
│   ├── building_and_running                                         |   |
│   ├── contributing                                                 |   |
│   ├── conversion                                                   |   |
│   ├── data_plane                                                   |   |
│   ├── example_code                                                 |   |
│   ├── extraction                                                   |   |
│   ├── flow_dispositions                                            |   |
│   ├── forwarding_analysis                                          |   |
│   ├── intellij_setup                                               |   |
│   ├── lab_notes                                                    |   |
│   ├── parsing                                                      |   |
│   ├── post_processing                                              |   |
│   ├── proposals                                                    |   |
│   ├── question_development                                         |   |
│   ├── README.md                                                    |   |
│   ├── symbolic_engine                                              |   |
│   └── topology                                                     |   |
├── networks             ### network topology and configuration      |   |
│   ├── BUILD.bazel                                                  |   |
│   ├── example                                                      |   |
│   │   ├── candidate                                                |   |
│   │   ├── example_layer1_topology.json                             |   |
│   │   ├── example-network.png                                      |   |
│   │   ├── live   --------------------------------------------+     |   |
│   │   ├── live-with-bgp-announcements                        |     |   |
│   │   ├── live-with-interface-outage                         |     |   |
│   │   ├── live-with-isp                                      |     |   |
│   │   ├── README.md                                          |     |   |
│   │   └── route-analysis   ------------------------------+   |     |   |
│   │       └── configs                                    |   |     |   |
│   │           ├── border1.cfg   -------------------------|---|-----+   |
│   │           └── border2.cfg   -------------------------|---|---------+
│   ├── hybrid-cloud-aws                                   |   |
│   └── iptables-firewall                                  |   |
├── projects             ### Batfish source code           |   |
│   ├── allinone                                           |   |
│   ├── batfish                                            |   |
│   ├── batfish-client                                     |   |
│   ├── batfish-common-protocol                            |   |
│   ├── bdd                                                |   |
│   ├── BUILD.bazel                                        |   |
│   ├── checkstyle.xml                                     |   |
│   ├── client                                             |   |
│   ├── coordinator                                        |   |
│   ├── minesweeper                                        |   |
│   ├── question                                           |   |
│   ├── symbolic                                           |   |
│   └── VERSION                                            |   |
├── README.md            ### README by yongzheng           |   |
├── README_original.md   ### original README by Batfish    |   |
├── tests                                                  |   |
│   ├── aws                                                |   |
│   ├── basic                                              |   |
│   ├── logging                                            |   |
│   ├── parsing-errors-tests                               |   |
│   ├── parsing-tests                                      |   |
│   ├── questions                                          |   |
│   ├── roles                                              |   |
│   └── test             ### test cases via pybatfish      |   |
│       ├── test_batfish_0001.py   <-----------------------|---+
│       └── test_routing_policies_0001.py   <--------------+
└── tools                ### tools involves some script
    ├── bazel_run.sh
    ├── bdd
    ├── benchmarks
    ├── BUILD.bazel
    ├── fix_java_format.sh
    ├── generate_pan_apps.py
    ├── jol
    ├── log4j2.yaml
    ├── README.md
    ├── run_checkstyle.sh
    ├── stress_tests
    ├── update_aws_addresses.sh
    ├── update_javadoc.sh
    └── update_refs.sh
```

### <b>Testing</b>

#### Execute Routing Policies Test Case

```sh
# open a terminal to build and run batfish service
$ cd /PATH-TO/batfish
$ tools/bazel_run.sh
# or open batfish in IntelliJ IDEA
# run //projects/allinone:allinone_main

# you can modify the input configuration in `./networks/example/routing-analysis`

# open another terminal to execute batfish query via pybatfish
$ cd /PATH-TO/batfish/tests/test
$ python3 test_routing_policies_0001.py
      Node  ...                                         Trace
0  border2  ...  - Matched route-map from_customer clause 400

[1 rows x 7 columns]

# you can refer the relevant output in the last `./bdds/routing_policies_xxxx`
```
