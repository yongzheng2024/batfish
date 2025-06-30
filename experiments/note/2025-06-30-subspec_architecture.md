1. slice smt encoding via [target variables] and [final variables] (i.e. (not xxx) in network verification)

2. extract intermediate variables' definition

3. inline intermediate variables' definition

4. construct dependency graph (all ite / => (or q not p) / ... expressions)

```cpp
// a expression

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

// Node structure

A : [
    |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|
    (= |0_FAILED-EDGE_r1_r2| 0)
    (= |0_FAILED-NODE_r1| 0)
]

True_branch : [
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
]

False_branch : [
    (not |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted|)
]
```

5. like topo-sort to parse this dependency graph

6. get final subspec (maybe empty subspec)