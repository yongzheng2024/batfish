#### Router Configuration

The configuration files for the routers border1 and border2 are stored in the directory `0_routing_policies_configs`.

#### Routing Policies Run Script

> Firstly, run the command `tools/bazel_run.sh` to build and run batfish server.

You can use the command `python3 0_test_routing_policies_0001.py` to run test case test\_routing\_policies\_0001. Every time you run the command, the output files (i.e., BDD encoding, SMT encoding and link between configuration variables and SMT variables) are stored in the most recently generated directory `routing_policies_xxxx`.

#### Output Directory Structure

```sh
routing_policies_0000          # minesweeper searchRoutePolicies output directory
├── border1                      # router border1
│   ├── bdd_encoding               # bdd encoding about symbolic route analysis
│   ├── link_configuration         # link between configurations and smt variables
│   └── smt_encoding               # shadow smt encoding about symbolic route analysis
│                                  # shadow smt encoding is created based on bdd encoding
└── border2                      # router border2
    ├── bdd_encoding               # ...
    ├── link_configuration         # ...
    └── smt_encoding               # ...
```

#### Link Configuration Parse

```txt
###### actual configuration (partial) ######
ip prefix-list private-ips seq 5 permit 10.0.0.0/8 ge 8   -------------------+
ip prefix-list private-ips seq 10 permit 172.16.0.0/12 ge 12   ----------+   |
ip prefix-list private-ips seq 15 permit 192.168.0.0/16 ge 16   -----+   |   |
!                                                                    |   |   |
route-map from_customer deny 100                                     |   |   |
 match ip address prefix-list private-ips   ------+                  |   |   |
                                                  |                  |   |   |
omitting ...                                      |                  |   |   |
                                                  |                  |   |   |
                                                  |                  |   |   |
###### link_configuration (partial) ######        |                  |   |   |
[]: If                                            |                  |   |   |
    []: MatchPrefixSet                            |                  |   |   |
        []: Named: private-ips   <----------------+                  |   |   |
        --- match_filter_list_1                                      |   |   |
        []: Prefix Range: 192.168.0.0/16:16-32   <-------------------+   |   |
        []: Action: PERMIT   <---------------------------------------+   |   |
        --- config_prefix_ip_2         # present relevant configuration  |   |
                                       # `192.168.0.0/16`                |   |
        --- config_prefix_length_3     # present relevant configuration  |   |
                                       # `ge 16`, i.e. 16 - 32           |   |
        --- match_prefix_ip_4                                            |   |
        --- match_prefix_length_5                                        |   |
        --- config_action_permit_6     # present `permit`                |   |
        []: Prefix Range: 172.16.0.0/12:12-32   <------------------------+   |
        []: Action: PERMIT   <-------------------------------------------+   |
        --- config_prefix_ip_7         # ...                                 |
        --- config_prefix_length_8     # ...                                 |
        --- match_prefix_ip_9                                                |
        --- match_prefix_length_10                                           |
        --- config_action_permit_11    # ...                                 |
        []: Prefix Range: 10.0.0.0/8:8-32   <--------------------------------+
        []: Action: PERMIT   <-----------------------------------------------+
        --- config_prefix_ip_12        # ...
        --- config_prefix_length_13    # ...
        --- match_prefix_ip_14
        --- match_prefix_length_15
        --- config_action_permit_16    # ...
        --- unmatched_17               # unmatched scenario
    []: ReturnFalse

omitting ...
```
