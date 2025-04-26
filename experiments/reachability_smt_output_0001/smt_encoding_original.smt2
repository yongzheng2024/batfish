(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1__reachable-id_as1core1| () Int)
(declare-fun |0_SLICE-as1core1__reachable_as1core1| () Bool)
(declare-fun |0_SLICE-as1core1__reachable-id_as1border1| () Int)
(declare-fun |0_SLICE-as1core1__reachable_as1border1| () Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1__reachable-id_as1core1| () Int)
(declare-fun |0_SLICE-as1border1__reachable_as1core1| () Bool)
(declare-fun |0_SLICE-as1border1__reachable-id_as1border1| () Int)
(declare-fun |0_SLICE-as1border1__reachable_as1border1| () Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_FAILED-EDGE_as1border1_as1core1| () Int)
(declare-fun |0_FAILED-EDGE_as1border1_as2border1| () Int)
(declare-fun |0_FAILED-EDGE_as1core1_Loopback0| () Int)
(declare-fun |0_FAILED-EDGE_as2border1_Loopback0| () Int)
(declare-fun |0_FAILED-EDGE_as1core1_GigabitEthernet0/0| () Int)
(declare-fun |0_FAILED-EDGE_as1border1_Loopback0| () Int)
(declare-fun |0_FAILED-EDGE_as2border1_GigabitEthernet1/0| () Int)
(declare-fun |0_FAILED-EDGE_as2border1_GigabitEthernet2/0| () Int)
(declare-fun |0_FAILED-NODE_as1border1| () Int)
(declare-fun |0_FAILED-NODE_as1core1| () Int)
(declare-fun |0_FAILED-NODE_as2border1| () Int)
(declare-fun |0_SLICE-MAIN_dst-port| () Int)
(declare-fun |0_SLICE-MAIN_src-port| () Int)
(declare-fun |0_SLICE-MAIN_icmp-type| () Int)
(declare-fun |0_SLICE-MAIN_ip-protocol| () Int)
(declare-fun |0_SLICE-MAIN_icmp-code| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_dst-ip| () (_ BitVec 32))
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_bgpInternal|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_2:1|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_1:2|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history|
             ()
             (_ BitVec 1))
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_2:1| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_1:2| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_choice| () Bool)
(declare-fun |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_choice| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal| () Bool)
(declare-fun |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal| () Bool)
(declare-fun |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_as2border1_OSPF_BEST_None_ospfType| () (_ BitVec 2))
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet2/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet1/0| () Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet0/0| () Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1border1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1border1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1border1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as2border1_Loopback0| () Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet2/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_dst-port| () Int)
(declare-fun |0_SLICE-as1border1_src-port| () Int)
(declare-fun |0_SLICE-as1border1_icmp-type| () Int)
(declare-fun |0_SLICE-as1border1_ip-protocol| () Int)
(declare-fun |0_SLICE-as1border1_icmp-code| () Int)
(declare-fun |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist| () Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric| () Int)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1border1_dst-ip| () (_ BitVec 32))
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
             ()
             (_ BitVec 1))
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_Loopback0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_iBGP-as1core1|
             ()
             Bool)
(declare-fun |0_SLICE-as1border1_DATA-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_dst-port| () Int)
(declare-fun |0_SLICE-as1core1_src-port| () Int)
(declare-fun |0_SLICE-as1core1_icmp-type| () Int)
(declare-fun |0_SLICE-as1core1_ip-protocol| () Int)
(declare-fun |0_SLICE-as1core1_icmp-code| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist| () Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric| () Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             ()
             Int)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted| () Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1core1_dst-ip| () (_ BitVec 32))
(declare-fun |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
             ()
             (_ BitVec 2))
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history|
             ()
             (_ BitVec 1))
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_iBGP-as1core1|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1core1_GigabitEthernet0/0|
             ()
             Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1core1_Loopback0| () Bool)
(declare-fun |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet1/0|
             ()
             Bool)
(declare-fun |0_SLICE-MAIN__reachable-id_as1core1| () Int)
(declare-fun |0_SLICE-MAIN__reachable_as1core1| () Bool)
(declare-fun |0_SLICE-MAIN__reachable-id_as1border1| () Int)
(declare-fun |0_SLICE-MAIN__reachable_as1border1| () Bool)
(declare-fun |0_SLICE-MAIN__reachable-id_as2border1| () Int)
(declare-fun |0_SLICE-MAIN__reachable_as2border1| () Bool)
(assert (bvule |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b10))
(assert (bvule |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId| #b10))
(assert (bvule |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId| #b10))
(assert (= |0_SLICE-as1core1__reachable_as1core1|
   (not (<= |0_SLICE-as1core1__reachable-id_as1core1| 0))))
(assert (>= |0_SLICE-as1core1__reachable-id_as1core1| 0))
(assert (= |0_SLICE-as1core1__reachable_as1border1|
   (not (<= |0_SLICE-as1core1__reachable-id_as1border1| 0))))
(assert (>= |0_SLICE-as1core1__reachable-id_as1border1| 0))
(assert (= |0_SLICE-as1core1__reachable-id_as1core1| 1))
(assert (let ((a!1 (not (and |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
                     (not (<= |0_SLICE-as1core1__reachable-id_as1core1| 0))))))
  (ite (and |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
            (not (<= |0_SLICE-as1core1__reachable-id_as1core1| 0)))
       (or (not (<= |0_SLICE-as1core1__reachable-id_as1border1|
                    |0_SLICE-as1core1__reachable-id_as1core1|))
           a!1)
       (= |0_SLICE-as1core1__reachable-id_as1border1| 0))))
(assert (= |0_SLICE-as1border1__reachable_as1core1|
   (not (<= |0_SLICE-as1border1__reachable-id_as1core1| 0))))
(assert (>= |0_SLICE-as1border1__reachable-id_as1core1| 0))
(assert (= |0_SLICE-as1border1__reachable_as1border1|
   (not (<= |0_SLICE-as1border1__reachable-id_as1border1| 0))))
(assert (>= |0_SLICE-as1border1__reachable-id_as1border1| 0))
(assert (= |0_SLICE-as1border1__reachable-id_as1border1| 1))
(assert (let ((a!1 (not (and |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
                     (not (<= |0_SLICE-as1border1__reachable-id_as1border1| 0))))))
  (ite (and |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
            (not (<= |0_SLICE-as1border1__reachable-id_as1border1| 0)))
       (or (not (<= |0_SLICE-as1border1__reachable-id_as1core1|
                    |0_SLICE-as1border1__reachable-id_as1border1|))
           a!1)
       (= |0_SLICE-as1border1__reachable-id_as1core1| 0))))
(assert (>= |0_FAILED-EDGE_as1border1_as1core1| 0))
(assert (<= |0_FAILED-EDGE_as1border1_as1core1| 1))
(assert (>= |0_FAILED-EDGE_as1border1_as2border1| 0))
(assert (<= |0_FAILED-EDGE_as1border1_as2border1| 1))
(assert (>= |0_FAILED-EDGE_as1core1_Loopback0| 0))
(assert (<= |0_FAILED-EDGE_as1core1_Loopback0| 1))
(assert (>= |0_FAILED-EDGE_as2border1_Loopback0| 0))
(assert (<= |0_FAILED-EDGE_as2border1_Loopback0| 1))
(assert (>= |0_FAILED-EDGE_as1core1_GigabitEthernet0/0| 0))
(assert (<= |0_FAILED-EDGE_as1core1_GigabitEthernet0/0| 1))
(assert (>= |0_FAILED-EDGE_as1border1_Loopback0| 0))
(assert (<= |0_FAILED-EDGE_as1border1_Loopback0| 1))
(assert (>= |0_FAILED-EDGE_as2border1_GigabitEthernet1/0| 0))
(assert (<= |0_FAILED-EDGE_as2border1_GigabitEthernet1/0| 1))
(assert (>= |0_FAILED-EDGE_as2border1_GigabitEthernet2/0| 0))
(assert (<= |0_FAILED-EDGE_as2border1_GigabitEthernet2/0| 1))
(assert (= |0_FAILED-EDGE_as1border1_as1core1| 0))
(assert (= |0_FAILED-EDGE_as1border1_as2border1| 0))
(assert (= |0_FAILED-EDGE_as1core1_Loopback0| 0))
(assert (= |0_FAILED-EDGE_as2border1_Loopback0| 0))
(assert (= |0_FAILED-EDGE_as1core1_GigabitEthernet0/0| 0))
(assert (= |0_FAILED-EDGE_as1border1_Loopback0| 0))
(assert (= |0_FAILED-EDGE_as2border1_GigabitEthernet1/0| 0))
(assert (= |0_FAILED-EDGE_as2border1_GigabitEthernet2/0| 0))
(assert (>= |0_FAILED-NODE_as1border1| 0))
(assert (<= |0_FAILED-NODE_as1border1| 1))
(assert (>= |0_FAILED-NODE_as1core1| 0))
(assert (<= |0_FAILED-NODE_as1core1| 1))
(assert (>= |0_FAILED-NODE_as2border1| 0))
(assert (<= |0_FAILED-NODE_as2border1| 1))
(assert (= |0_FAILED-NODE_as1border1| 0))
(assert (= |0_FAILED-NODE_as1core1| 0))
(assert (= |0_FAILED-NODE_as2border1| 0))
(assert (>= |0_SLICE-MAIN_dst-port| 0))
(assert (>= |0_SLICE-MAIN_src-port| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_dst-port|)))
(assert (not (<= 65536 |0_SLICE-MAIN_src-port|)))
(assert (>= |0_SLICE-MAIN_icmp-type| 0))
(assert (>= |0_SLICE-MAIN_ip-protocol| 0))
(assert (not (<= 256 |0_SLICE-MAIN_icmp-type|)))
(assert (<= |0_SLICE-MAIN_ip-protocol| 256))
(assert (>= |0_SLICE-MAIN_icmp-code| 0))
(assert (not (<= 16 |0_SLICE-MAIN_icmp-code|)))
(assert (>= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref| 0))
(assert (not (<= 4294967296 |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric| 0))
(assert (>= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|
    0))
(assert (<= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|
    32))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength| 32))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist| 0))
(assert (not (<= 256 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref| 0))
(assert (not (<= 4294967296
         |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric| 0))
(assert (not (<= 65536 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)))
(assert (>= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength| 32))
(assert (= (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
       |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_2:1|)
   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:|))
(assert (= (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
       |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_2:1|)
   |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:|))
(assert (= (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
       |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_2:1|)
   |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:|))
(assert (= (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
       |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_2:1|)
   |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:|))
(assert (ite (and |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1core1| 0))
     (and (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             (+ 1 |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)))
(assert (let ((a!1 (ite (or (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002))
                (and |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric| 0)
                     (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                        24)
                     (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                (ite (and |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1border1| 0))
                     (and (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|)
                          (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|)
                          (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|)
                          (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|)
                          (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|))
                     (not |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|)))))
  (ite (= |0_SLICE-MAIN_dst-ip| #x010a0101)
       (and |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist| 110)
            (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 32)
            (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00))
       a!1)))
(assert (ite (and (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1|)
          |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
          |0_SLICE-as1core1__reachable_as1border1|
          (= |0_FAILED-NODE_as1core1| 0))
     (and (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_clientId|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_1:2|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_1:2|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_2:1|
             |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_2:1|)
          |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|
          (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|
             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|))
     (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|)))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric|
                   (ite (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history|
                           #b01)
                        |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
                        0))
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_1:2|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_2:1|
                   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1|)
                |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_bgpInternal|)))
  (ite (and |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-NODE_as1border1| 0))
       (ite (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b01)
            a!1
            (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|))
       (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|))))
(assert (ite (and (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1core1| 0))
     (and |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
          (= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|
             24))
     (not |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|)))
(assert (ite (and |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1border1| 0))
     (and (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             (+ 1 |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)))
(assert (let ((a!1 (or (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b00)
               (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b10)
                    (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                            0)))))
      (a!2 (ite (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                        #b10)
                     (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                             0)))
                20
                |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|))
      (a!3 (ite (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                        #b10)
                     (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                             0)))
                #b11
                |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|)))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|)
                (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric|
                   (ite (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                           #b00)
                        |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                        a!2))
                (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType|
                   (ite (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                           #b00)
                        |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
                        a!3)))))
  (ite a!1 a!4 (not |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|)))))
(assert (let ((a!1 (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                        24))
               (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                       24)
                    (not (<= 110
                             |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|)))))
      (a!2 (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                        32))
               (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                       32)
                    (not (<= 110
                             |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|)))))
      (a!3 (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|)
                (or (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType|
                       |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|)
                    (not (bvule |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|
                                |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType|))))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|
                             |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|
                             |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|))
                    a!4))))
(let ((a!6 (and |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|))
                    a!5))))
(let ((a!7 (ite (and |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
                     (not a!6))
                (ite (and |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1core1| 0))
                     (and (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|))
                     (not |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|))
                (ite (and |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1core1| 0))
                     (and (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength|
                             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist|
                             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric|
                             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType|
                             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType|)
                          (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                             |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|))
                     (not |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|)))))
(let ((a!8 (ite (and (= |0_SLICE-MAIN_dst-ip| #x01010101)
                     (not (and |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                               a!2)))
                (and |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric| 0)
                     (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                        32)
                     (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                a!7)))
  (ite (and (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
            (not (and |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
                      a!1)))
       (and |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist| 110)
            (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 24)
            (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType| #b00))
       a!8))))))))
(assert (let ((a!1 (ite |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:|
                (and (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|)
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength|)
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist|)
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|
                        (ite |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:|
                             350
                             |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref|))
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric|)
                     (ite (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId|
                             #b00)
                          (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|
                             #b10)
                          (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|
                             |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId|))
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_1:2|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_1:2|)
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                     (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_2:1|
                        |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_2:1|)
                     (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|))
                (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|))))
  (ite (and (not |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet0/0|)
            |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
            (= |0_FAILED-EDGE_as1border1_as2border1| 0)
            (= |0_FAILED-NODE_as1border1| 0))
       a!1
       (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|))))
(assert (let ((a!1 (or (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
               (and (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                    (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                            #b01)))
               (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| 24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002)
                    (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                            #b01)))))
      (a!2 (and (not (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001))
                (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength| 0)))
      (a!3 (and (or (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                       24))
                (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)))
      (a!4 (and (or (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                       24))
                (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002)))
      (a!5 (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
              (ite (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                   24
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|))))
(let ((a!6 (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|)
                a!5
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric|
                   (ite (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                           #b01)
                        (+ 1 |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|)
                        1))
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId|
                   #b00)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_1:2|
                   (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|
                       a!2
                       a!3
                       a!4))
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_2:1|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|)
                (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|))))
  (ite (and |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_as1border1_as2border1| 0)
            (= |0_FAILED-NODE_as2border1| 0))
       (ite (and a!1 (or a!2 a!3 a!4))
            a!6
            (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|))
       (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|)))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_1:2|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_1:2|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_2:1|
                   |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_2:1|)
                |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|
                (or (not (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId|
                            #b01))
                    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|
                       |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|)))))
  (ite (and (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|)
            |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
            |0_SLICE-as1border1__reachable_as1core1|
            (= |0_FAILED-NODE_as1border1| 0))
       a!1
       (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|))))
(assert (let ((a!1 (or (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
               (and (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
                    (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                            #b01)))
               (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| 24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002)
                    (not (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                            #b01)))))
      (a!2 (ite (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|
                        24)
                     (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002))
                24
                |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|)))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength|
                   a!2)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric|
                   (ite (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history|
                           #b01)
                        |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                        0))
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_clientId|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_1:2|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_2:1|
                   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|)
                |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_bgpInternal|)))
  (ite (and (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|)
            |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-NODE_as1core1| 0))
       (ite a!1
            a!3
            (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|))
       (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|)))))
(assert (ite (and (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001)
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1border1| 0))
     (and |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
          (= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|
             24))
     (not |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|)))
(assert (not |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|))
(assert (let ((a!1 (or (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
                       24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001))
               (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
                       24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002))))
      (a!2 (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_1:2|
               (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
                       24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001))
               (and (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
                       24)
                    (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010002)))))
(let ((a!3 (ite a!1
                (and (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|)
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|)
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist|)
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|
                        (ite a!1
                             350
                             |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref|))
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric|)
                     (ite (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId|
                             #b00)
                          (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|
                             #b00)
                          (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|
                             |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId|))
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_1:2|
                        a!2)
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                     (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_2:1|
                        |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_2:1|))
                (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|))))
  (ite (and (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|)
            |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
            (= |0_FAILED-EDGE_as1border1_as2border1| 0)
            (= |0_FAILED-NODE_as2border1| 0))
       a!3
       (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|)))))
(assert (let ((a!1 (and (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| 17)
                (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| 32)
                (= ((_ extract 31 16) |0_SLICE-MAIN_dst-ip|) #x0280)))
      (a!2 (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_2:1|
               (and (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                        16)
                    (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                        32)
                    (= ((_ extract 31 23) |0_SLICE-MAIN_dst-ip|) #b000000101)))))
(let ((a!3 (and (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric|
                   (ite (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history|
                           #b1)
                        (+ 1 |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|)
                        1))
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId|
                   #b00)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_1:2|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_1:2|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
                   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
                (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_2:1|
                   a!2))))
(let ((a!4 (ite (and (or (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history|
                            #b1)
                         a!1)
                     (not a!1)
                     (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b1)
                     (>= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                         16)
                     (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                         32)
                     (= ((_ extract 31 23) |0_SLICE-MAIN_dst-ip|) #b000000101))
                a!3
                (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|))))
  (ite (and |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_as1border1_as2border1| 0)
            (= |0_FAILED-NODE_as1border1| 0))
       a!4
       (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|
                   |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
                (or (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|
                       |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
                    (not (bvule |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
                                |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
                             |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
      (not (<= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
   |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
    (and |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
         (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|
                             |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|))
                    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|
                       |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|
                   |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)
                (or (and |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|
                         (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|
                   |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|
                             |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|
                             |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|
                             |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|)
      (not (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|))
      a!5)))))))
(assert (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
   |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|)
    (and |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_1:2|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_1:2|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_2:1|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_2:1|))))
(assert (or (not |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|)
    (= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|
       |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|)
    (not (<= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|
             |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|))))
(assert (= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
   |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|)
    (and |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
         (= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|
                   |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
                (or (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|
                       |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
                    (not (bvule |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
                                |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
                             |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
    (and |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
         (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|))
                    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|
                       |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)
                (or (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|
                         (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
                             |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|))
      a!5)))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|))
                    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| 0)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)
                (or (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|
                         (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
                             |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|))
      a!5)))))))
(assert (= (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
       |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|)
   |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|))
(assert (or (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_1:2|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_1:2|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_2:1|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_2:1|))
    (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| 0)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_1:2|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_1:2|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_2:1|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_2:1|))
    (not (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
             |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|))))
(assert (or (not |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|)
    (= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|
       |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|)
    (not (<= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|
             |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|))))
(assert (= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
   |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|)
    (and |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
         (= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|
                   |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)
                (or (not (<= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|
                             |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|))
                    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|
                       |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|
                   |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|
                             |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|
                             |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|)
      (not (<= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|
               |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
   |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|))
(assert (or (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|)
    (and |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_1:2|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_1:2|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_2:1|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_2:1|))))
(assert (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
   (and |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
        (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
        (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|
           |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
        (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|
           |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
        (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|
           |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_choice|
   (and |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|)
        (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|
           |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|))))
(assert (= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_choice|
   (and |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
        (= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|))))
(assert (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
   (and |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
        (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
        (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|
           |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
        (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|
           |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
        (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|
           |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_choice|
   (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|))))
(assert (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_choice|
   (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId|
           |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|)
        (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| 0))))
(assert (= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|
   (and |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
        (= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|
           |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|))))
(assert (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_choice|
   (and |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
        (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|
           |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|)
        (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|
           |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)
        (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|
           |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)
        (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|
           |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)
        (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId|
           |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)
                (or (not (bvule |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|
                                |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|))
                    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|)
                (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
                (or (not (<= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
                             100))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|))
      a!5)))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|))
                    (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|
                            |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|)
                         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|)
                (or (and |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|
                         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
                   |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
                             |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|))
      a!5)))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0)
                (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|))
                    (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|
                            0)
                         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
                (or (not (<= 0 |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0)
                (or (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
                             100))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|))
                    a!3))))
  (or (not |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|))
      a!4))))))
(assert (= (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
       |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
       |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|)
   |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|))
(assert (or (and |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2|)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1|))
    (and |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_1:2|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1|
            |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_2:1|))
    (and |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b10)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2|)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1|))
    (not (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
             |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
             |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)
                (or (not (bvule |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|
                                |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|))
                    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|)))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|)
                (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                             100))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|))
      a!5)))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|))
                    (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|
                            |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|)
                         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|)
                (or (and |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|
                         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                   |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                             |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|))
                    a!4))))
  (or (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|))
      a!5)))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0)
                (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|))
                    (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|
                            0)
                         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0)
                (or (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                             100))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|)
                (or (not (<= 0
                             |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|))
                    a!3))))
  (or (not |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|))
      a!4))))))
(assert (= (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
       |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
       |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|)
   |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|))
(assert (or (and |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|))
    (and |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_1:2|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|
            |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_2:1|))
    (and |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|))
    (not (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
             |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
             |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric|)
                (or (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-MAIN_as2border1_OSPF_BEST_None_ospfType|)
                    (not (bvule |0_SLICE-MAIN_as2border1_OSPF_BEST_None_ospfType|
                                |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref| 100)
                (or (not (<= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric|
                             |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
                             100))
                    a!2))))
(let ((a!4 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist|
                             |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|))
                    a!3))))
  (or (not |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength|))
      a!4))))))
(assert (let ((a!1 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
                   |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|)
                (or (not (<= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|
                             |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|))
                    (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
                            |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|)
                         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
                             |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|
                             |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|)
      (not (<= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|))
      a!3)))))
(assert (= (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
       |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|)
   |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|))
(assert (or (and |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-MAIN_as2border1_OSPF_BEST_None_ospfType|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b0)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId| #b00)
         (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_1:2|)
         (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_2:1|))
    (and |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b1)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_1:2|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_1:2|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_2:1|
            |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_2:1|))
    (not (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
             |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
    (not (and |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b00)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
    (not (and |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_choice|
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b01)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|
                 |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|)))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
    (not (and (= |0_SLICE-MAIN_dst-ip| #x01000101)
              |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_choice|
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b10)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
              (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)))))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_Loopback0|))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|)
    (and |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0))
    (and (= |0_SLICE-MAIN_dst-ip| #x01000101)
         |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_choice|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b10)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0))))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|)
    (and |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_choice|
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b01)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId|)
         (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric|))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
    (not (and |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b00)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1|
    (not (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_choice|
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|)))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
    (not (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_choice|
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                 |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
    (not (and (= |0_SLICE-MAIN_dst-ip| #x01000102)
              |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b10)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
              (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)))))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_Loopback0|))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|)
    (and |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0))
    (and (= |0_SLICE-MAIN_dst-ip| #x01000102)
         |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 100)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b10)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0))))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|)
    (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_choice|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0))))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1|)
    (and |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_choice|
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b01)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId|)
         (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric|
            |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric|))))
(assert (or |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet0/0|
    (not (and |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_choice|
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
                 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
                 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType| #b00)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b1)
              (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId|
                 |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|)))))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_Loopback0|))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet2/0|))
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet1/0|))
(assert (or (not |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet0/0|)
    (and |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_choice|
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b1)
         (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId|
            |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId|))))
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
       (and |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
            |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|))
   |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet1/0|))
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
       (and |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
            |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet0/0|))
   |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_Loopback0|
       (and |0_SLICE-MAIN_CONTROL-FORWARDING_as1core1_iBGP-as1border1|
            |0_SLICE-as1border1_DATA-FORWARDING_as1core1_Loopback0|))
   |0_SLICE-MAIN_DATA-FORWARDING_as1core1_Loopback0|))
(assert (let ((a!1 (and |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1|
                (or (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                            #b01)
                         |0_SLICE-as1core1_DATA-FORWARDING_as1border1_Loopback0|)
                    (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                            #b10)
                         |0_SLICE-as1border1_DATA-FORWARDING_as1border1_Loopback0|)))))
  (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_Loopback0| a!1)
     |0_SLICE-MAIN_DATA-FORWARDING_as1border1_Loopback0|)))
(assert (let ((a!1 (and |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_iBGP-as1core1|
                (or (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                            #b01)
                         |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|)
                    (and (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId|
                            #b10)
                         |0_SLICE-as1border1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|)))))
  (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0| a!1)
     |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet0/0|)))
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
   |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet1/0|))
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet0/0|
   |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet0/0|))
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_Loopback0|
   |0_SLICE-MAIN_DATA-FORWARDING_as2border1_Loopback0|))
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet2/0|
   |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet2/0|))
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_as2border1_GigabitEthernet1/0|
   |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet1/0|))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_history| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_OVERALL_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_BEST_None_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_history| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_OVERALL_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_BEST_None_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_permitted|
    (= |0_SLICE-MAIN_as1border1_CONNECTED_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_history| #b0)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_OVERALL_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as2border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_OSPF_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_localPref| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_metric| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_BEST_None_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_1:2|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_BEST_None_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_BEST_None_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_EXPORT_iBGP-as1border1_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_metric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (= |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_permitted|
    (not |0_SLICE-MAIN_as1core1_BGP_IMPORT_iBGP-as1border1_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1core1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|
       0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-MAIN_as1border1_OSPF_Redistributed_ospfType| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_GigabitEthernet1/0_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_GigabitEthernet1/0_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_EXPORT_iBGP-as1core1_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_localPref| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_metric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_bgpInternal|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (= |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_igpMetric| 0)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_1:2|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_permitted|
    (not |0_SLICE-MAIN_as1border1_BGP_IMPORT_iBGP-as1core1_community_2:1|)))
(assert (or |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as1border1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|
       0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_localPref| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_1:2|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_EXPORT_GigabitEthernet0/0_community_2:1|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_adminDist| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_localPref| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_prefixLength| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_metric| 0)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_clientId| #b00)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_1:2|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )2:_OTHER|)))
(assert (or |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_permitted|
    (not |0_SLICE-MAIN_as2border1_BGP_IMPORT_GigabitEthernet0/0_community_2:1|)))
(assert (= |0_SLICE-MAIN_dst-ip| #x01000102))
(assert (>= |0_SLICE-as1border1_dst-port| 0))
(assert (>= |0_SLICE-as1border1_src-port| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_dst-port|)))
(assert (not (<= 65536 |0_SLICE-as1border1_src-port|)))
(assert (>= |0_SLICE-as1border1_icmp-type| 0))
(assert (>= |0_SLICE-as1border1_ip-protocol| 0))
(assert (not (<= 256 |0_SLICE-as1border1_icmp-type|)))
(assert (<= |0_SLICE-as1border1_ip-protocol| 256))
(assert (>= |0_SLICE-as1border1_icmp-code| 0))
(assert (not (<= 16 |0_SLICE-as1border1_icmp-code|)))
(assert (>= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0))
(assert (not (<= 256
         |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0))
(assert (not (<= 65536
         |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)))
(assert (>= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
    32))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist| 0))
(assert (not (<= 256
         |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0))
(assert (not (<= 65536
         |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
    0))
(assert (<= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
    32))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric|)))
(assert (>= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength| 32))
(assert (>= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength| 0))
(assert (<= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength| 32))
(assert (ite (and |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1core1| 0))
     (and (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             (+ 1 |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)))
(assert (let ((a!1 (ite (or (= ((_ extract 31 8) |0_SLICE-as1border1_dst-ip|) #x010001)
                    (= ((_ extract 31 8) |0_SLICE-as1border1_dst-ip|) #x010002))
                (and |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric|
                        0)
                     (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                        24)
                     (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                (ite (and |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1border1| 0))
                     (and (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|)
                          (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|)
                          (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|)
                          (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|)
                          (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|))
                     (not |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|)))))
  (ite (= |0_SLICE-as1border1_dst-ip| #x010a0101)
       (and |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 110)
            (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
               32)
            (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00))
       a!1)))
(assert (ite (and |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1border1| 0))
     (and (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             (+ 1 |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)))
(assert (let ((a!1 (or (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b0)
               (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                       #b1)
                    (not (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                            0)))))
      (a!2 (ite (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                        #b1)
                     (not (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                             0)))
                20
                |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|))
      (a!3 (ite (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                        #b1)
                     (not (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                             0)))
                #b11
                |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|)))
(let ((a!4 (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                   |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                   |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|)
                (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|
                   |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|)
                (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric|
                   (ite (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                           #b0)
                        |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
                        a!2))
                (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType|
                   (ite (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                           #b0)
                        |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
                        a!3)))))
  (ite a!1
       a!4
       (not |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|)))))
(assert (let ((a!1 (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                        24))
               (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                       24)
                    (not (<= 110
                             |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|)))))
      (a!2 (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                        32))
               (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                       32)
                    (not (<= 110
                             |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|)))))
      (a!3 (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|)
                (or (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType|
                       |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|)
                    (not (bvule |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
                                |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType|))))))
(let ((a!4 (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|
                             |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric|))
                    a!3))))
(let ((a!5 (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|
                             |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|))
                    a!4))))
(let ((a!6 (and |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|))
                    a!5))))
(let ((a!7 (ite (and |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
                     (not a!6))
                (ite (and |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1core1| 0))
                     (and (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|))
                     (not |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|))
                (ite (and |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1core1| 0))
                     (and (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength|
                             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist|
                             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric|
                             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType|
                             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|)
                          (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                             |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|))
                     (not |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|)))))
(let ((a!8 (ite (and (= |0_SLICE-as1border1_dst-ip| #x01010101)
                     (not (and |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                               a!2)))
                (and |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric|
                        0)
                     (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                        32)
                     (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                a!7)))
  (ite (and (= ((_ extract 31 8) |0_SLICE-as1border1_dst-ip|) #x010001)
            (not (and |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
                      a!1)))
       (and |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
               110)
            (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
               24)
            (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
               #b00))
       a!8))))))))
(assert (ite (and (= |0_SLICE-as1border1_dst-ip| #x01010101)
          (= |0_FAILED-EDGE_as1border1_Loopback0| 0)
          (= |0_FAILED-NODE_as1border1| 0))
     (and |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
          (= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|
             32))
     (not |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|)))
(assert true)
(assert (let ((a!1 (and (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|
                   |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
                (or (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
                    (not (bvule |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
                                |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
                (or (not (<= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
                (or (not (<= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
                             |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
      (not (<= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
   |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
    (and |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (let ((a!1 (and (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|
                   |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
                (or (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
                       |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
                    (not (bvule |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
                                |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|
                   |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|
                   |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
                             |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
      (not (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|
               |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
    (and |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
         (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (or (not |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|)
    (= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|
       |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|)
    (not (<= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|
             |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
   |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|)
    (and |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
         (= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
   (and |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
        (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
           |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
        (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|
           |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
        (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|
           |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
        (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
           |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
   (and |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
        (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|
           |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
        (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|
           |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
        (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|
           |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
        (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
           |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_choice|
   (and |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
        (= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|
           |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (let ((a!1 (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|)
                (or (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|)
                    (not (bvule |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|
                                |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|
                             |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|
                             |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|)
      (not (<= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|))
      a!3)))))
(assert (let ((a!1 (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
                   0)
                (or (not (<= 0
                             |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|))
                    (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
                            0)
                         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|)
                (or (not (<= 0
                             |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|))
                    a!1))))
  (or (not |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|)
      (not (<= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|))
      a!2))))
(assert (= (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
       |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|)
   |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|))
(assert (or (and |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b0))
    (and |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b1))
    (not (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
             |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|))))
(assert (or |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
    (not (and |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
              (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
              (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
              (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|
                 |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
              (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)))))
(assert (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_Loopback0|))
(assert (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_iBGP-as1border1|))
(assert (or (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|)
    (and |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (or |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
    (not (and |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
              (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
              (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
              (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
                 |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
              (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
              (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b0)))))
(assert (let ((a!1 (not (and (not (= |0_SLICE-as1border1_dst-ip| #x01010101))
                     |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_choice|
                     (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
                        |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|)
                     (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
                        0)
                     (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
                        0)
                     (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
                        #b00)
                     (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history|
                        #b1)))))
  (or |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_Loopback0| a!1)))
(assert (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|))
(assert (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_iBGP-as1core1|))
(assert (or (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|)
    (and |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b0))))
(assert (or (not |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_Loopback0|)
    (and (not (= |0_SLICE-as1border1_dst-ip| #x01010101))
         |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_choice|
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b1))))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1core1_Loopback0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1core1_Loopback0|))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_Loopback0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1border1_Loopback0|))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1border1_GigabitEthernet1/0|))
(assert (= |0_SLICE-as1border1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
   |0_SLICE-as1border1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|))
(assert (or |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1core1_OVERALL_BEST_None_ospfType| #b00)))
(assert true)
(assert (or |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OVERALL_BEST_None_history| #b0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_permitted|
    (= |0_SLICE-as1border1_as1border1_CONNECTED_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
       0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0)))
(assert (or |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1border1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
       #b00)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
       0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
       0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
       #b00)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_adminDist| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_prefixLength| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_metric| 0)))
(assert (or |0_SLICE-as1border1_as1border1_OSPF_Redistributed_permitted|
    (= |0_SLICE-as1border1_as1border1_OSPF_Redistributed_ospfType| #b00)))
(assert (or |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_permitted|
    (= |0_SLICE-as1border1_as1border1_CONNECTED_IMPORT_Loopback0_prefixLength|
       0)))
(assert (and (= |0_SLICE-as1border1_dst-ip| #x01010101)
     (= |0_SLICE-as1border1_dst-port| 179)
     (= |0_SLICE-as1border1_ip-protocol| 6)))
(assert (>= |0_SLICE-as1core1_dst-port| 0))
(assert (>= |0_SLICE-as1core1_src-port| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_dst-port|)))
(assert (not (<= 65536 |0_SLICE-as1core1_src-port|)))
(assert (>= |0_SLICE-as1core1_icmp-type| 0))
(assert (>= |0_SLICE-as1core1_ip-protocol| 0))
(assert (not (<= 256 |0_SLICE-as1core1_icmp-type|)))
(assert (<= |0_SLICE-as1core1_ip-protocol| 256))
(assert (>= |0_SLICE-as1core1_icmp-code| 0))
(assert (not (<= 16 |0_SLICE-as1core1_icmp-code|)))
(assert (>= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|)))
(assert (>= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0))
(assert (not (<= 256
         |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0))
(assert (not (<= 65536
         |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)))
(assert (>= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0))
(assert (not (<= 256 |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist|)))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric| 0))
(assert (not (<= 65536 |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric|)))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 32))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist| 0))
(assert (not (<= 256
         |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0))
(assert (not (<= 65536
         |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)))
(assert (>= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength| 0))
(assert (<= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
    32))
(assert (ite (and |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1core1| 0))
     (and (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
             |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
             |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
             |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
             (+ 1 |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
             |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)))
(assert (let ((a!1 (ite (or (= ((_ extract 31 8) |0_SLICE-as1core1_dst-ip|) #x010001)
                    (= ((_ extract 31 8) |0_SLICE-as1core1_dst-ip|) #x010002))
                (and |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric|
                        0)
                     (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                        24)
                     (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                (ite (and |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1border1| 0))
                     (and (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|)
                          (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|)
                          (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|)
                          (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|)
                          (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|))
                     (not |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|)))))
  (ite (= |0_SLICE-as1core1_dst-ip| #x010a0101)
       (and |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 110)
            (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 32)
            (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00))
       a!1)))
(assert (ite (and (= |0_SLICE-as1core1_dst-ip| #x010a0101)
          (= |0_FAILED-EDGE_as1core1_Loopback0| 0)
          (= |0_FAILED-NODE_as1core1| 0))
     (and |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
          (= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|
             32))
     (not |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|)))
(assert (ite (and |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
          (= |0_FAILED-NODE_as1border1| 0))
     (and (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
             |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|)
          (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
             |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength|)
          (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
             |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist|)
          (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
             (+ 1 |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric|))
          (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
             |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType|))
     (not |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)))
(assert (let ((a!1 (ite (= |0_SLICE-as1core1_dst-ip| #x01010101)
                (and |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
                     (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                        110)
                     (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric|
                        0)
                     (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                        32)
                     (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                        #b00))
                (ite (and |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|
                          (= |0_FAILED-EDGE_as1border1_as1core1| 0)
                          (= |0_FAILED-NODE_as1core1| 0))
                     (and (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|)
                          (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|)
                          (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|)
                          (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|)
                          (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|))
                     (not |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|)))))
  (ite (= ((_ extract 31 8) |0_SLICE-as1core1_dst-ip|) #x010001)
       (and |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
            (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist| 110)
            (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric| 0)
            (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength|
               24)
            (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType| #b00))
       a!1)))
(assert true)
(assert (let ((a!1 (and (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|
                   |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
                (or (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|
                       |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
                    (not (bvule |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|
                                |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|
                   |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
                (or (not (<= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|
                   |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
                (or (not (<= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|
                             |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
      a!3
      (not (<= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|
               |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)))))))
(assert (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
   |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|)
    (and |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
         (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (or (not |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|)
    (= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|
       |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|)
    (not (<= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|
             |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
   |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|)
    (and |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
         (= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (let ((a!1 (and (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|
                   |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
                (or (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)
                    (not (bvule |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
                                |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
                (or (not (<= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
                (or (not (<= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|
                             |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
      (not (<= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|))
      a!3)))))
(assert (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
   |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|))
(assert (or (not |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|)
    (and |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
   (and |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
        (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|
           |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
        (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|
           |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
        (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|
           |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
        (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|
           |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|))))
(assert (= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_choice|
   (and |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
        (= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|
           |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|))))
(assert (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
   (and |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
        (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
           |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
        (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|
           |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
        (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|
           |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
        (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
           |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (let ((a!1 (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|
                   |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|)
                (or (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
                       |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|)
                    (not (bvule |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|
                                |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|))))))
(let ((a!2 (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|
                   |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|)
                (or (not (<= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|
                             |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|))
                    a!1))))
(let ((a!3 (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|)
                (or (not (<= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|
                             |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|))
                    a!2))))
  (or (not |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|)
      (not (<= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|))
      a!3)))))
(assert (let ((a!1 (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| 0)
                (or (not (<= 0
                             |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|))
                    (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|
                            0)
                         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
                            #b00))))))
(let ((a!2 (and (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|)
                (or (not (<= 0
                             |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|))
                    a!1))))
  (or (not |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|)
      (not (<= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
               |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|))
      a!2))))
(assert (= (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
       |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|)
   |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|))
(assert (or (and |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b0))
    (and |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b1))
    (not (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
             |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|))))
(assert (or |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
    (not (and |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
              (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
              (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
              (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|
                 |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
              (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
              (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b0)))))
(assert (let ((a!1 (not (and (not (= |0_SLICE-as1core1_dst-ip| #x010a0101))
                     |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_choice|
                     (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
                        |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|)
                     (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|
                        0)
                     (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| 0)
                     (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
                        #b00)
                     (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history|
                        #b1)))))
  (or |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_Loopback0| a!1)))
(assert (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_iBGP-as1border1|))
(assert (or (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|)
    (and |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_choice|
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b0))))
(assert (or (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_Loopback0|)
    (and (not (= |0_SLICE-as1core1_dst-ip| #x010a0101))
         |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_choice|
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength|)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| 0)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| 0)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType| #b00)
         (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b1))))
(assert (or |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
    (not (and |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
              (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
                 |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
              (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|
                 |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
              (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|
                 |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
              (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
                 |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|)))))
(assert (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_Loopback0|))
(assert (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|))
(assert (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_iBGP-as1core1|))
(assert (or (not |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|)
    (and |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_choice|
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric|)
         (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType|
            |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|))))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet1/0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1core1_GigabitEthernet1/0|))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_GigabitEthernet0/0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1core1_GigabitEthernet0/0|))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1core1_Loopback0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1core1_Loopback0|))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_Loopback0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1border1_Loopback0|))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet1/0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet1/0|))
(assert (= |0_SLICE-as1core1_CONTROL-FORWARDING_as1border1_GigabitEthernet0/0|
   |0_SLICE-as1core1_DATA-FORWARDING_as1border1_GigabitEthernet0/0|))
(assert (or |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OVERALL_BEST_None_history| #b0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_BEST_None_ospfType| #b00)))
(assert (or |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1core1_CONNECTED_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_metric| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_permitted|
    (= |0_SLICE-as1core1_as1border1_OVERALL_BEST_None_ospfType| #b00)))
(assert true)
(assert (or |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_prefixLength|
       0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_metric| 0)))
(assert (or |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_permitted|
    (= |0_SLICE-as1core1_as1core1_OSPF_IMPORT_GigabitEthernet1/0_ospfType| #b00)))
(assert (or |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_permitted|
    (= |0_SLICE-as1core1_as1core1_CONNECTED_IMPORT_Loopback0_prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__prefixLength| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__metric| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_SINGLE-EXPORT__ospfType| #b00)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_adminDist| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_prefixLength|
       0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_metric| 0)))
(assert (or |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_permitted|
    (= |0_SLICE-as1core1_as1border1_OSPF_IMPORT_GigabitEthernet0/0_ospfType|
       #b00)))
(assert (and (= |0_SLICE-as1core1_dst-ip| #x010a0101)
     (= |0_SLICE-as1core1_dst-port| 179)
     (= |0_SLICE-as1core1_ip-protocol| 6)))
(assert (= |0_SLICE-MAIN__reachable_as1core1|
   (not (<= |0_SLICE-MAIN__reachable-id_as1core1| 0))))
(assert (>= |0_SLICE-MAIN__reachable-id_as1core1| 0))
(assert (= |0_SLICE-MAIN__reachable_as1border1|
   (not (<= |0_SLICE-MAIN__reachable-id_as1border1| 0))))
(assert (>= |0_SLICE-MAIN__reachable-id_as1border1| 0))
(assert (= |0_SLICE-MAIN__reachable_as2border1|
   (not (<= |0_SLICE-MAIN__reachable-id_as2border1| 0))))
(assert (>= |0_SLICE-MAIN__reachable-id_as2border1| 0))
(assert (let ((a!1 (not (and |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
                     (not (<= |0_SLICE-MAIN__reachable-id_as1border1| 0))))))
(let ((a!2 (ite (and |0_SLICE-MAIN_DATA-FORWARDING_as1core1_GigabitEthernet1/0|
                     (not (<= |0_SLICE-MAIN__reachable-id_as1border1| 0)))
                (or (not (<= |0_SLICE-MAIN__reachable-id_as1core1|
                             |0_SLICE-MAIN__reachable-id_as1border1|))
                    a!1)
                (= |0_SLICE-MAIN__reachable-id_as1core1| 0))))
  (ite (and |0_SLICE-MAIN_as1core1_CONNECTED_BEST_None_permitted|
            (= |0_SLICE-MAIN_dst-ip| #x01000102))
       (= |0_SLICE-MAIN__reachable-id_as1core1| 1)
       a!2))))
(assert (let ((a!1 (or (and |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
                    (not (<= |0_SLICE-MAIN__reachable-id_as1core1| 0)))
               (and |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet1/0|
                    (not (<= |0_SLICE-MAIN__reachable-id_as2border1| 0)))))
      (a!2 (not (and |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet0/0|
                     (not (<= |0_SLICE-MAIN__reachable-id_as1core1| 0)))))
      (a!3 (not (and |0_SLICE-MAIN_DATA-FORWARDING_as1border1_GigabitEthernet1/0|
                     (not (<= |0_SLICE-MAIN__reachable-id_as2border1| 0))))))
(let ((a!4 (and (or (not (<= |0_SLICE-MAIN__reachable-id_as1border1|
                             |0_SLICE-MAIN__reachable-id_as1core1|))
                    a!2)
                (or (not (<= |0_SLICE-MAIN__reachable-id_as1border1|
                             |0_SLICE-MAIN__reachable-id_as2border1|))
                    a!3))))
  (ite a!1 a!4 (= |0_SLICE-MAIN__reachable-id_as1border1| 0)))))
(assert (let ((a!1 (not (and |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet0/0|
                     (not (<= |0_SLICE-MAIN__reachable-id_as1border1| 0))))))
  (ite (and |0_SLICE-MAIN_DATA-FORWARDING_as2border1_GigabitEthernet0/0|
            (not (<= |0_SLICE-MAIN__reachable-id_as1border1| 0)))
       (or (not (<= |0_SLICE-MAIN__reachable-id_as2border1|
                    |0_SLICE-MAIN__reachable-id_as1border1|))
           a!1)
       (= |0_SLICE-MAIN__reachable-id_as2border1| 0))))
(assert (not |0_SLICE-MAIN__reachable_as2border1|))
(assert (or (not (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #x010001))
    (= |0_FAILED-EDGE_as1border1_as1core1| 0)))
(assert (= |0_FAILED-EDGE_as1core1_GigabitEthernet0/0| 0))
(assert (= |0_FAILED-EDGE_as1core1_Loopback0| 0))
(assert true)
(assert (= |0_FAILED-EDGE_as1border1_Loopback0| 0))
(assert true)
(assert (= |0_FAILED-EDGE_as2border1_Loopback0| 0))
(assert (= |0_FAILED-EDGE_as2border1_GigabitEthernet2/0| 0))
(assert (= |0_FAILED-EDGE_as2border1_GigabitEthernet1/0| 0))

(check-sat)
;(get-model)
