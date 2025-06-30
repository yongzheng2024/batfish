## ITE Expression 1
```cpp
(and 
    (or 
        |0_SLICE-MAIN_isp1_BGP_BEST_None_permitted| 
        |0_SLICE-MAIN_isp1_CONNECTED_BEST_None_permitted| 
        |0_SLICE-MAIN_isp1_STATIC_BEST_None_permitted|
    ) 
    (= 0 0) 
    (= 0 0)
)
```

### |0_SLICE-MAIN_isp1_BGP_BEST_None_permitted| 

```cpp
(assert 
    (= 
        |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted|
        |0_SLICE-MAIN_isp1_BGP_BEST_None_permitted|
    )
)

(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet2/0|)
            |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_permitted|
            (= |0_FAILED-EDGE_isp1_r1| 0)
            (= |0_FAILED-NODE_isp1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_permitted|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_prefixLength| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_prefixLength|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_localPref| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_localPref|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_metric| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_metric|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_community_200:100| 
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_200:100|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_community_300:100|
               |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_300:100|)
        )
        (not |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted|)
    )
)

(assert 
    (ite 
        (and 
            |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted| 
            (= |0_FAILED-EDGE_isp1_r1| 0) 
            (= |0_FAILED-NODE_isp1| 0)
        ) 
        (ite 
            (and 
                (>= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| Config_r1_RouteFilterList_default_ips__Line1__0_0_0_0__prefix_range_start) (<= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| Config_r1_RouteFilterList_default_ips__Line1__0_0_0_0__prefix_range_end) Config_r1_RouteFilterList_default_ips__Line1__0_0_0_0__action
            ) 
            (and 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_permitted| |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_prefixLength| |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_localPref| |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_metric| (+ 1 |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric|)) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\{\|\}\|^\|$\| )300:_OTHER| 
                   |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\{\|\}\|^\|$\| )300:_OTHER|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_200:100| 
                   |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_200:100|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\{\|\}\|^\|$\| )200:_OTHER| 
                   |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\{\|\}\|^\|$\| )200:_OTHER|) 
                (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_300:100| 
                   |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_300:100|) 
                (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_bgpInternal|)
            ) 
            (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_permitted|)
        ) 
        (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_permitted|)
    )
)

(assert 
    (= 
        (or 
            |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted| 
            |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted| 
            |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_permitted| 
            |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_permitted| 
            |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted| 
            |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted|
        ) 
        |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|
    )
)
```

#### |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted| 

```cpp
(assert 
    (ite 
        (and 
            |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_r1_r2| 0)
            (= |0_FAILED-NODE_r1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_prefixLength|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_localPref|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_metric|
               (+ 1 |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric|))
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_200:100|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_300:100|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_300:100|)
            (not |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|)
        )
        (not |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted|)
    )
)

(assert 
    (= 
        (or 
            |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet2/0_permitted|
            |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_permitted|
            |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_permitted|
            |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_permitted|
            |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_permitted|
        )
        |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|
    )
)
```

#### |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted| 

```cpp
(assert 
    (ite 
        (and 
            |0_SLICE-MAIN_r3_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_r1_r3| 0)
            (= |0_FAILED-NODE_r1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_prefixLength|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_localPref|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_metric|
               (+ 1 |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric|))
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_200:100|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_300:100|
               |0_SLICE-MAIN_r3_OVERALL_BEST_None_community_300:100|)
            (not |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|)
        )
        (not |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted|)
    )
)

(assert 
    (= 
        (or 
            |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_permitted|
            |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_permitted|
            |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet3/0_permitted|
            |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_permitted|
            |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_permitted|
            |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_permitted|
        )
        |0_SLICE-MAIN_r3_OVERALL_BEST_None_permitted|
    )
)
```

#### |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_permitted| 

```cpp
(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet1/0|) 
            |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__permitted| 
            (= |0_FAILED-EDGE_isp2_r1| 0) 
            (= |0_FAILED-NODE_r1| 0)
        ) 
        (ite 
            (ite 
                (and 
                    (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength|      
                        Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_start) 
                    (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                        Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_end) 
                    (= 
                        (bvnot 
                            (bvor 
                                (bvnot |0_SLICE-MAIN_dst-ip|) 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                            )
                        ) 
                        (bvnot 
                            (bvor 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__ip) 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                            )
                        )
                    )
                ) 
                Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__action 
                (and 
                    (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                        Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_start) 
                    (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                        Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_end) 
                    (= 
                        (bvnot 
                            (bvor 
                                (bvnot |0_SLICE-MAIN_dst-ip|) 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                            )
                        ) 
                        (bvnot 
                            (bvor 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__ip) 
                                (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                            )
                        )
                    ) 
                    Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__action
                )
            ) 
            (and 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_permitted| |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__permitted|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_prefixLength| |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_localPref| 
                    (ite 
                        (ite 
                            (and 
                                (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_start) 
                                (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_end) 
                                (= 
                                    (bvnot 
                                        (bvor 
                                            (bvnot |0_SLICE-MAIN_dst-ip|) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                                        )
                                    ) 
                                    (bvnot 
                                        (bvor 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__ip) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                                        )
                                    )
                                )
                            ) 
                            Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__action 
                            (and 
                                (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_start) 
                                (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_end) 
                                (= 
                                    (bvnot 
                                        (bvor 
                                            (bvnot |0_SLICE-MAIN_dst-ip|) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                                        )
                                    ) 
                                    (bvnot 
                                        (bvor 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__ip) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                                        )
                                    )
                                ) 
                                Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__action
                            )
                        ) 
                        Config_r1_RoutingPolicy_as3_to_as1__Line1__set_localpreference_350 
                        |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__localPref|
                    )
                ) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_metric| |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__metric|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_community_(,\|\{\|\}\|^\|$\| )300:_OTHER| 
                   |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_(,\|\{\|\}\|^\|$\| )300:_OTHER|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_community_200:100| 
                   |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_200:100|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_community_(,\|\{\|\}\|^\|$\| )200:_OTHER| 
                   |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_(,\|\{\|\}\|^\|$\| )200:_OTHER|) 
                (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_community_300:100| 
                    (ite 
                        (ite 
                            (and 
                                (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_start) 
                                (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__prefix_range_end) 
                                (= 
                                    (bvnot 
                                        (bvor 
                                            (bvnot |0_SLICE-MAIN_dst-ip|) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                                        )
                                    ) 
                                    (bvnot 
                                        (bvor 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__ip) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__mask)
                                        )
                                    )
                                )
                            ) 
                            Config_r1_RouteFilterList_isp_network__Line1__192_0_2_0__action 
                            (and 
                                (>= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_start) 
                                (<= |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__prefixLength| 
                                    Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__prefix_range_end) 
                                (= 
                                    (bvnot 
                                        (bvor 
                                            (bvnot |0_SLICE-MAIN_dst-ip|) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                                        )
                                    ) 
                                    (bvnot 
                                        (bvor 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__ip) 
                                            (bvnot Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__mask)
                                        )
                                    )
                                ) 
                                Config_r1_RouteFilterList_isp_network__Line2__198_51_100_0__action
                            )
                        ) 
                        Config_r1_RoutingPolicy_as3_to_as1__Line1__add_community_300_100_community 
                        |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_300:100|
                    )
                ) 
                (not |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_bgpInternal|)
            ) 
            (not |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_permitted|)
        ) 
        (not |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet3/0_permitted|)
    )
)
```


#### |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_permitted| 


#### |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted| 

```cpp
(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1|)
            |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_permitted|
            |0_SLICE-r1__reachable_r2|
            (= |0_FAILED-NODE_r1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_prefixLength|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_localPref|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_metric|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_metric|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_community_200:100|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_community_300:100|
               |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_300:100|)
            |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_bgpInternal|
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_igpMetric|
               |0_SLICE-r2_r1_OVERALL_BEST_None_metric|)
        )
        (not |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted|)
    )
)
```

##### |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1|

```cpp
// p => q (not p or q)
(assert 
    (or 
        |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1|
        (not 
            (and 
                |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_choice|
                (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength|
                   |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_prefixLength|)
                (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref|
                   |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_localPref|)
                (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric|
                   |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_metric|)
                (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal|
                   |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_bgpInternal|)
                (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric|
                   |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_igpMetric|)
            )
        )
    )
)
```

##### |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_permitted|

```cpp
(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal|)
            |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|
            (= |0_FAILED-NODE_r1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_permitted|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_prefixLength|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_localPref|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_metric|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_200:100|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_300:100|
               |0_SLICE-MAIN_r2_OVERALL_BEST_None_community_300:100|)
            |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_bgpInternal|
        )
        (not |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_permitted|)
    )
)
```

##### |0_SLICE-r1__reachable_r2|

```cpp
(assert 
    (= 
        |0_SLICE-r1__reachable_r2| 
        (not (<= |0_SLICE-r1__reachable-id_r2| 0))
    )
)

(assert 
    (ite 
        (or 
            (and 
                |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0| 
                (not (<= |0_SLICE-r1__reachable-id_r1| 0))
            ) 
            (and 
                |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0| 
                (not (<= |0_SLICE-r1__reachable-id_r3| 0))
            )
        ) 
        (and 
            (or 
                (not (<= |0_SLICE-r1__reachable-id_r2| |0_SLICE-r1__reachable-id_r1|)) 
                (not (and |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0| (not (<= |0_SLICE-r1__reachable-id_r1| 0))))
            ) 
            (or 
                (not (<= |0_SLICE-r1__reachable-id_r2| |0_SLICE-r1__reachable-id_r3|)) 
                (not (and |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0| (not (<= |0_SLICE-r1__reachable-id_r3| 0))))
            )
        ) 
        (= |0_SLICE-r1__reachable-id_r2| 0)
    )
)
```

#### |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted|

```cpp
(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r1|)
            |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_permitted|
            |0_SLICE-r1__reachable_r3|
            (= |0_FAILED-NODE_r1| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_prefixLength|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_localPref|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_metric|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_metric|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_community_200:100|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_community_300:100|
               |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_300:100|)
            |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_bgpInternal|
            (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_igpMetric|
               |0_SLICE-r3_r1_OVERALL_BEST_None_metric|))
        (not |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted|)
    )
)
```

#### |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|

```cpp
(assert (>= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| 32))

(assert 
    (ite 
        (and 
            |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_r1_r3| 0)
            (= |0_FAILED-NODE_r3| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_permitted| 
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_prefixLength|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_localPref|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_metric|
               (+ 1 |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric|))
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_200:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_300:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_300:100|)
            (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|)
        )
        (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_permitted|)
    )
)


(assert 
    (ite 
        (and 
            |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_r1_r2| 0)
            (= |0_FAILED-NODE_r2| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_permitted|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_localPref|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_metric|
               (+ 1 |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric|))
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_200:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_300:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_300:100|)
            (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|)
        )
        (not |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_permitted|)
    )
)

(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal|)
            |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-NODE_r2| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_permitted|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_prefixLength|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_localPref|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_metric|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_200:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_300:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_300:100|)
            |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_bgpInternal|
        )
        (not |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_permitted|)
    )
)

(assert 
    (ite 
        (and 
            (not |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal|)
            |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-NODE_r3| 0)
        )
        (and 
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_permitted|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_prefixLength|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_localPref|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_metric|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_200:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_300:100|
               |0_SLICE-MAIN_r1_OVERALL_BEST_None_community_300:100|)
            |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_bgpInternal|
        )
        (not |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_permitted|)
    )
)
```


### |0_SLICE-MAIN_isp1_CONNECTED_BEST_None_permitted| 

```cpp
(assert 
    (= 
        |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_permitted|
        |0_SLICE-MAIN_isp1_CONNECTED_BEST_None_permitted|
    )
)

(assert
    (ite 
        (and 
            (= ((_ extract 31 7) |0_SLICE-MAIN_dst-ip|) #b1100000000000000000000100)
            (= |0_FAILED-EDGE_isp1_GigabitEthernet3/0| 0)
            (= |0_FAILED-NODE_isp1| 0)
        )
        (and 
            |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_permitted|
            (= |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_prefixLength| 25)
        )
        (not |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_permitted|)
    )
)

(assert (= ((_ extract 31 7) |0_SLICE-MAIN_dst-ip|) #b1100000000000000000000100))  // 0xC000020
```

### |0_SLICE-MAIN_isp1_STATIC_BEST_None_permitted|

```cpp
(assert 
    (= 
        |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_permitted|
        |0_SLICE-MAIN_isp1_STATIC_BEST_None_permitted|
    )
)

(assert 
    (ite 
        (and 
            (= ((_ extract 31 8) |0_SLICE-MAIN_dst-ip|) #xc00002)
            (= |0_FAILED-EDGE_isp1_GigabitEthernet3/0| 0)
            (= |0_FAILED-NODE_isp1| 0)
        )
        (and 
            |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_permitted|
            (= |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_prefixLength| 24))
        (not |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_permitted|)
    )
)

(assert (= ((_ extract 31 7) |0_SLICE-MAIN_dst-ip|) #b1100000000000000000000100))  // 0xC000020
```


## ITE Expression 2

```cpp
(or 
    (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00) 
    (and 
        (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start) 
        (= 
            (bvnot 
                (bvor 
                    (bvnot |0_SLICE-MAIN_dst-ip|) 
                    (bvnot #xffffff00)
                )
            ) 
            (bvnot 
                (bvor 
                    (bvnot #xc0000200) 
                    (bvnot #xffffff00)
                )
            )
        ) 
        (not 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
        )
    )
) 
```

### |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history|

```cpp
// BGP (#b00), CONNECTED (#b01), STATIC (#b10)
(assert (bvule |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b10))

(assert 
    (or 
        |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted| 
        (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
    )
)

(assert 
    (or 
        (not |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet3/0|) 
        (and 
            |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_choice| 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength| 
               |0_SLICE-MAIN_isp1_STATIC_IMPORT_GigabitEthernet3/0_prefixLength|) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_adminDist| 1) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_localPref| 100) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_metric| 0) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b10)
        ) 
        (and 
            (not (= |0_SLICE-MAIN_dst-ip| #xc0000201)) 
            |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_choice| 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength| 
               |0_SLICE-MAIN_isp1_CONNECTED_IMPORT_GigabitEthernet3/0_prefixLength|) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_adminDist| 0) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_localPref| 100) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_metric| 0) 
            (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b01)
        )
    )
)
```
