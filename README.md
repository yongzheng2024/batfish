### <b>>Configure Batfish and Pybatfish</b>

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

> [PyBatfish usage document](https://pybatfish.readthedocs.io/en/latest/getting_started.html)
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
bf.init_snapshot(SNAPSHOT_DIR, name=SNAPSHOT_NAME, overwrite=True)
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
# then edit Configurations and add bazel command
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

# you can check network and snapshot via URL
# http://localhost:9996/v2/networks
```

### Directory Structure

#### Partial Directory Structure via Tree Command

```txt
Batfish
├── bdds                 ### bdd encode output (order from 000 to 999)
│   ├── routing_policies_000.txt
│   └── routing_policies_001.txt
├── docs                 ### documents
│   ├── building_and_running
│   ├── contributing
│   ├── conversion
│   ├── data_plane
│   ├── example_code
│   ├── extraction
│   ├── flow_dispositions
│   ├── forwarding_analysis
│   ├── intellij_setup
│   ├── lab_notes
│   ├── parsing
│   ├── post_processing
│   ├── proposals
│   ├── question_development
│   ├── README.md
│   ├── symbolic_engine
│   └── topology
├── networks             ### network topology and router configuration
│   ├── BUILD.bazel
│   ├── example
│   │   ├── candidate
│   │   ├── example_layer1_topology.json
│   │   ├── example-network.png
│   │   ├── live   -------------------------------------------+
│   │   ├── live-with-bgp-announcements                       |
│   │   ├── live-with-interface-outage                        |
│   │   ├── live-with-isp                                     |
│   │   ├── README.md                                         |
│   │   └── route-analysis   ------------------------------+  |
│   ├── hybrid-cloud-aws                                   |  |
│   └── iptables-firewall                                  |  |
├── projects             ### Batfish source code           |  |
│   ├── allinone                                           |  |
│   ├── batfish                                            |  |
│   ├── batfish-client                                     |  |
│   ├── batfish-common-protocol                            |  |
│   ├── bdd                                                |  |
│   ├── BUILD.bazel                                        |  |
│   ├── checkstyle.xml                                     |  |
│   ├── client                                             |  |
│   ├── coordinator                                        |  |
│   ├── minesweeper                                        |  |
│   ├── question                                           |  |
│   ├── symbolic                                           |  |
│   └── VERSION                                            |  |
├── README.md            ### README by yongzheng           |  |
├── README_original.md   ### original README by Batfish    |  |
├── tests                                                  |  |
│   ├── aws                                                |  |
│   ├── basic                                              |  |
│   ├── logging                                            |  |
│   ├── parsing-errors-tests                               |  |
│   ├── parsing-tests                                      |  |
│   ├── questions                                          |  |
│   ├── roles                                              |  |
│   └── test             ### test cases via pybatfish      |  |
│       ├── test_batfish_0001.py   <-----------------------|--+
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

# you can refer the bdd encode output in the last `./bdds/routing_policies_xxx.txt`
```
