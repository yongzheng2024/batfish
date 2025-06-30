```cpp
(assert 
    (let 
        ((a!1 
            (= 
                (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
            )
        ))
        (let 
            ((a!2 
                (or 
                    (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
                    (and (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start)
                         (= 
                             (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                                          (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                             (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                                          (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                         )
                         (not (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00))
                    )
                )
            )
            (a!3 
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__prefixLength|
                    (ite 
                        (and 
                            (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start)
                            (= 
                                (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                                (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                            )
                        )
                        24
                        |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength|
                    )
                )
            ))
(let ((a!4 
        (and 
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__permitted|
               |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|)
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__prefixLength|
                (ite 
                    (and 
                        (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start)
                        (= 
                            (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                                         (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                            (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                                         (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                        )
                    )
                    24
                    |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength|
                )
            )
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__localPref| |0_SLICE-MAIN_isp1_OVERALL_BEST_None_localPref|)
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__metric|
                (ite (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
                     (+ 1 |0_SLICE-MAIN_isp1_OVERALL_BEST_None_metric|)
                     1
                )
            )
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER| 
               |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_200:100|
               |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_200:100|)
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
               |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
            (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_300:100|
               |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_300:100|)
        )
    ))



  (ite (and |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|
            (= |0_FAILED-EDGE_isp1_r1| 0)
            (= |0_FAILED-NODE_r1| 0)
       )
       (ite 
            (or 
                (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
                (and (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start)
                     (= 
                         (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                                      (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                         (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                                      (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                     )
                     (not (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00))
                )
            )
            (and 
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__permitted|
                   |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|)
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__prefixLength|
                    (ite 
                        (and 
                            (= 24 Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__prefix_range_start)
                            (= 
                                (bvnot (bvor (bvnot |0_SLICE-MAIN_dst-ip|)
                                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                                (bvnot (bvor (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__ip)
                                             (bvnot Config_isp1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__192_0_2_0__mask)))
                            )
                        )
                        24
                        |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength|
                    )
                )
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__localPref| |0_SLICE-MAIN_isp1_OVERALL_BEST_None_localPref|)
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__metric|
                    (ite (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_history| #b00)
                         (+ 1 |0_SLICE-MAIN_isp1_OVERALL_BEST_None_metric|)
                         1
                    )
                )
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER| 
                   |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )300:_OTHER|)
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_200:100|
                   |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_200:100|)
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|
                   |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_(,\|\\{\|\\}\|^\|$\| )200:_OTHER|)
                (= |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_300:100|
                   |0_SLICE-MAIN_isp1_OVERALL_BEST_None_community_300:100|)
            )
            (not |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__permitted|))
       (not |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__permitted|))))))

```