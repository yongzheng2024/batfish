### <b>Install</b>

Batfish/Minesweeper depend on the following software.

* OpenJDK 11
* Bazel
* Z3
* Pytbatfish

You can directly run the command "./install.sh" to install these software in Ubuntu22.04 (tested) or macOS (to do test).

### <b>Test</b>

> [PyBatfish usage document](https://pybatfish.readthedocs.io/en/latest/getting_started.html) <br>
> [PyBatfish interact with the Batfish service](https://pybatfish.readthedocs.io/en/latest/notebooks/interacting.html#)

Open two terminals: one for running the Batfish service, and other for running a Pybatfish test case.

In the first terminal, start the Batfish service:
```sh
cd /PATH-TO/batfish
tools/bazel_run.sh
```

In the second terminal, run the Pybatfish test case:
```sh
cd /PATH-TO/tests/test
python3 test_routing_policies_0001.py
```

### <b>Configure Intellij IDEA</b>

> [IntelliJ IDEA configuration document](https://github.com/batfish/batfish/tree/master/docs/intellij_setup)

You can install plugins `Bazel For Intellij` and `Bazel (EAP)`. Then import the batfish directory from `file` - `import bazel project`.

You can configure bazel command in `Run/Debug configurations` according to following steps (modify `/PATH-TO/batfish` to your root directory of batfish).

* Target expression (Java\_binary handled by Java Handler)
    - //projects/allinone:allinone\_main
* Bazel command
    - run
* Bazel flags
    - --jvmopt=-Xmx12g
    - --jvmopt=-Dlog4j2.configurationFile=tools/log4j2.yaml
    - --java\_runtime\_version=11
    - --run\_under="cd /PATH-TO/batfish &&"
* Executable flags
    - -runclient
    - false
    - -coordinatorargs
    - "-templatedirs ./questions"
```

### Directory Structure (partial)

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
