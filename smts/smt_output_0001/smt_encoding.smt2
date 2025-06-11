(declare-fun |0_FAILED-EDGE_dest_~Interface_5~| () Int)
(declare-fun |0_FAILED-EDGE_dest_src| () Int)
(declare-fun |0_FAILED-EDGE_dest_~Interface_4~| () Int)
(declare-fun |0_FAILED-NODE_dest| () Int)
(declare-fun |0_FAILED-NODE_src| () Int)
(declare-fun |0_dst-port| () Int)
(declare-fun |0_src-port| () Int)
(declare-fun |0_icmp-type| () Int)
(declare-fun |0_ip-protocol| () Int)
(declare-fun |0_icmp-code| () Int)
(declare-fun |0_src_OVERALL_BEST_None_adminDist| () Int)
(declare-fun |0_src_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_src_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_src_CONNECTED_BEST_None_prefixLength| () Int)
(declare-fun |0_src_STATIC_BEST_None_prefixLength| () Int)
(declare-fun |0_dest_OVERALL_BEST_None_metric| () Int)
(declare-fun |0_dest_OVERALL_BEST_None_prefixLength| () Int)
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength| () Int)
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength| () Int)
(declare-fun |0_src_STATIC_IMPORT_~Interface_2~_prefixLength| () Int)
(declare-fun |0_src_STATIC_IMPORT_~Interface_0~_prefixLength| () Int)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength| () Int)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength| () Int)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength| () Int)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength| () Int)
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_2~_permitted| () Bool)
(declare-fun |0_dst-ip| () (_ BitVec 32))
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_0~_permitted| () Bool)
(declare-fun |0_src_STATIC_IMPORT_~Interface_2~_permitted| () Bool)
(declare-fun |0_src_STATIC_IMPORT_~Interface_0~_permitted| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted| () Bool)
(declare-fun |0_src_CONNECTED_BEST_None_permitted| () Bool)
(declare-fun |0_src_STATIC_BEST_None_permitted| () Bool)
(declare-fun |0_dest_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_2~_choice| () Bool)
(declare-fun |0_src_CONNECTED_IMPORT_~Interface_0~_choice| () Bool)
(declare-fun |0_src_STATIC_IMPORT_~Interface_2~_choice| () Bool)
(declare-fun |0_src_STATIC_IMPORT_~Interface_0~_choice| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_1~_choice| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_4~_choice| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_3~_choice| () Bool)
(declare-fun |0_dest_CONNECTED_IMPORT_~Interface_5~_choice| () Bool)
(declare-fun |0_src_OVERALL_BEST_None_permitted| () Bool)
(declare-fun |0_src_OVERALL_BEST_None_history| () (_ BitVec 1))
(declare-fun |0_CONTROL-FORWARDING_src_~Interface_2~| () Bool)
(declare-fun |0_CONTROL-FORWARDING_src_~Interface_0~| () Bool)
(declare-fun |0_CONTROL-FORWARDING_dest_~Interface_1~| () Bool)
(declare-fun |0_CONTROL-FORWARDING_dest_~Interface_4~| () Bool)
(declare-fun |0_CONTROL-FORWARDING_dest_~Interface_3~| () Bool)
(declare-fun |0_CONTROL-FORWARDING_dest_~Interface_5~| () Bool)
(declare-fun |0_DATA-FORWARDING_src_~Interface_2~| () Bool)
(declare-fun |0_DATA-FORWARDING_src_~Interface_0~| () Bool)
(declare-fun |0_DATA-FORWARDING_dest_~Interface_5~| () Bool)
(declare-fun |0_DATA-FORWARDING_dest_~Interface_1~| () Bool)
(declare-fun |0_DATA-FORWARDING_dest_~Interface_4~| () Bool)
(declare-fun |0_DATA-FORWARDING_dest_~Interface_3~| () Bool)
(declare-fun |0__reachable-id_src| () Int)
(declare-fun |0__reachable_src| () Bool)
(declare-fun |0__reachable-id_dest| () Int)
(declare-fun |0__reachable_dest| () Bool)
(assert (>= |0_FAILED-EDGE_dest_~Interface_5~| 0))
(assert (<= |0_FAILED-EDGE_dest_~Interface_5~| 1))
(assert (>= |0_FAILED-EDGE_dest_src| 0))
(assert (<= |0_FAILED-EDGE_dest_src| 1))
(assert (>= |0_FAILED-EDGE_dest_~Interface_4~| 0))
(assert (<= |0_FAILED-EDGE_dest_~Interface_4~| 1))
(assert (<= (+ |0_FAILED-EDGE_dest_~Interface_5~|
       |0_FAILED-EDGE_dest_src|
       |0_FAILED-EDGE_dest_~Interface_4~|)
    1))
(assert (>= |0_FAILED-NODE_dest| 0))
(assert (<= |0_FAILED-NODE_dest| 1))
(assert (>= |0_FAILED-NODE_src| 0))
(assert (<= |0_FAILED-NODE_src| 1))
(assert (= |0_FAILED-NODE_dest| 0))
(assert (= |0_FAILED-NODE_src| 0))
(assert (>= |0_dst-port| 0))
(assert (>= |0_src-port| 0))
(assert (not (<= 65536 |0_dst-port|)))
(assert (not (<= 65536 |0_src-port|)))
(assert (>= |0_icmp-type| 0))
(assert (>= |0_ip-protocol| 0))
(assert (not (<= 256 |0_icmp-type|)))
(assert (<= |0_ip-protocol| 256))
(assert (>= |0_icmp-code| 0))
(assert (not (<= 16 |0_icmp-code|)))
(assert (>= |0_src_OVERALL_BEST_None_adminDist| 0))
(assert (not (<= 256 |0_src_OVERALL_BEST_None_adminDist|)))
(assert (>= |0_src_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_src_OVERALL_BEST_None_metric|)))
(assert (>= |0_src_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_src_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_src_CONNECTED_BEST_None_prefixLength| 0))
(assert (<= |0_src_CONNECTED_BEST_None_prefixLength| 32))
(assert (>= |0_src_STATIC_BEST_None_prefixLength| 0))
(assert (<= |0_src_STATIC_BEST_None_prefixLength| 32))
(assert (>= |0_dest_OVERALL_BEST_None_metric| 0))
(assert (not (<= 65536 |0_dest_OVERALL_BEST_None_metric|)))
(assert (>= |0_dest_OVERALL_BEST_None_prefixLength| 0))
(assert (<= |0_dest_OVERALL_BEST_None_prefixLength| 32))
(assert (>= |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength| 0))
(assert (<= |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength| 32))
(assert (>= |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength| 0))
(assert (<= |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength| 32))
(assert (>= |0_src_STATIC_IMPORT_~Interface_2~_prefixLength| 0))
(assert (<= |0_src_STATIC_IMPORT_~Interface_2~_prefixLength| 32))
(assert (>= |0_src_STATIC_IMPORT_~Interface_0~_prefixLength| 0))
(assert (<= |0_src_STATIC_IMPORT_~Interface_0~_prefixLength| 32))
(assert (>= |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength| 0))
(assert (<= |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength| 32))
(assert (>= |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength| 0))
(assert (<= |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength| 32))
(assert (>= |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength| 0))
(assert (<= |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength| 32))
(assert (>= |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength| 0))
(assert (<= |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength| 32))
(assert (ite (and (= ((_ extract 31 1) |0_dst-ip|) #b0000001000000000000000000000000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_src| 0))
     (and |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
          (= |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength| 31))
     (not |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|)))
(assert (ite (and (= ((_ extract 31 1) |0_dst-ip|) #b0000000100000000000000000000000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_src| 0))
     (and |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|
          (= |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength| 31))
     (not |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|)))
(assert (ite (and (= |0_dst-ip| #x02010000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_src| 0))
     (and |0_src_STATIC_IMPORT_~Interface_2~_permitted|
          (= |0_src_STATIC_IMPORT_~Interface_2~_prefixLength| 32))
     (not |0_src_STATIC_IMPORT_~Interface_2~_permitted|)))
(assert (ite (and (= |0_dst-ip| #x01010000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_src| 0))
     (and |0_src_STATIC_IMPORT_~Interface_0~_permitted|
          (= |0_src_STATIC_IMPORT_~Interface_0~_prefixLength| 32))
     (not |0_src_STATIC_IMPORT_~Interface_0~_permitted|)))
(assert (ite (and (= |0_dst-ip| #x02010000)
          (= |0_FAILED-EDGE_dest_~Interface_5~| 0)
          (= |0_FAILED-NODE_dest| 0))
     (and |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
          (= |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength| 32))
     (not |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|)))
(assert (ite (and (= ((_ extract 31 1) |0_dst-ip|) #b0000000100000000000000000000000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_dest| 0))
     (and |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
          (= |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength| 31))
     (not |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|)))
(assert (ite (and (= |0_dst-ip| #x01010000)
          (= |0_FAILED-EDGE_dest_~Interface_4~| 0)
          (= |0_FAILED-NODE_dest| 0))
     (and |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
          (= |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength| 32))
     (not |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|)))
(assert (ite (and (= ((_ extract 31 1) |0_dst-ip|) #b0000001000000000000000000000000)
          (= |0_FAILED-EDGE_dest_src| 0)
          (= |0_FAILED-NODE_dest| 0))
     (and |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|
          (= |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength| 31))
     (not |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|)))
(assert true)
(assert (or (not |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|)
    (= |0_src_CONNECTED_BEST_None_prefixLength|
       |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|)
    (not (<= |0_src_CONNECTED_BEST_None_prefixLength|
             |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|))))
(assert (or (not |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|)
    (= |0_src_CONNECTED_BEST_None_prefixLength|
       |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|)
    (not (<= |0_src_CONNECTED_BEST_None_prefixLength|
             |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|))))
(assert (= (or |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
       |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|)
   |0_src_CONNECTED_BEST_None_permitted|))
(assert (or (and |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
         (= |0_src_CONNECTED_BEST_None_prefixLength|
            |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|))
    (and |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|
         (= |0_src_CONNECTED_BEST_None_prefixLength|
            |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|))
    (not (or |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
             |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|))))
(assert (or (not |0_src_STATIC_IMPORT_~Interface_2~_permitted|)
    (= |0_src_STATIC_BEST_None_prefixLength|
       |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|)
    (not (<= |0_src_STATIC_BEST_None_prefixLength|
             |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|))))
(assert (or (not |0_src_STATIC_IMPORT_~Interface_0~_permitted|)
    (= |0_src_STATIC_BEST_None_prefixLength|
       |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|)
    (not (<= |0_src_STATIC_BEST_None_prefixLength|
             |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|))))
(assert (= (or |0_src_STATIC_IMPORT_~Interface_2~_permitted|
       |0_src_STATIC_IMPORT_~Interface_0~_permitted|)
   |0_src_STATIC_BEST_None_permitted|))
(assert (or (and |0_src_STATIC_IMPORT_~Interface_2~_permitted|
         (= |0_src_STATIC_BEST_None_prefixLength|
            |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|))
    (and |0_src_STATIC_IMPORT_~Interface_0~_permitted|
         (= |0_src_STATIC_BEST_None_prefixLength|
            |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|))
    (not (or |0_src_STATIC_IMPORT_~Interface_2~_permitted|
             |0_src_STATIC_IMPORT_~Interface_0~_permitted|))))
(assert (let ((a!1 (and (= |0_dest_OVERALL_BEST_None_prefixLength|
                   |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|)
                (or (= |0_dest_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_dest_OVERALL_BEST_None_metric|))))))
  (or (not |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|)
      (not (<= |0_dest_OVERALL_BEST_None_prefixLength|
               |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|))
      a!1)))
(assert (let ((a!1 (and (= |0_dest_OVERALL_BEST_None_prefixLength|
                   |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|)
                (or (= |0_dest_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_dest_OVERALL_BEST_None_metric|))))))
  (or (not |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|)
      (not (<= |0_dest_OVERALL_BEST_None_prefixLength|
               |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|))
      a!1)))
(assert (let ((a!1 (and (= |0_dest_OVERALL_BEST_None_prefixLength|
                   |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|)
                (or (= |0_dest_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_dest_OVERALL_BEST_None_metric|))))))
  (or (not |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|)
      (not (<= |0_dest_OVERALL_BEST_None_prefixLength|
               |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|))
      a!1)))
(assert (let ((a!1 (and (= |0_dest_OVERALL_BEST_None_prefixLength|
                   |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|)
                (or (= |0_dest_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_dest_OVERALL_BEST_None_metric|))))))
  (or (not |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|)
      (not (<= |0_dest_OVERALL_BEST_None_prefixLength|
               |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|))
      a!1)))
(assert (= (or |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
       |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
       |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
       |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|)
   |0_dest_OVERALL_BEST_None_permitted|))
(assert (or (and |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))
    (and |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))
    (and |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))
    (and |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))
    (not (or |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
             |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
             |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
             |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|))))
(assert (= |0_src_CONNECTED_IMPORT_~Interface_2~_choice|
   (and |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
        (= |0_src_CONNECTED_BEST_None_prefixLength|
           |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|))))
(assert (= |0_src_CONNECTED_IMPORT_~Interface_0~_choice|
   (and |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|
        (= |0_src_CONNECTED_BEST_None_prefixLength|
           |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|))))
(assert (= |0_src_STATIC_IMPORT_~Interface_2~_choice|
   (and |0_src_STATIC_IMPORT_~Interface_2~_permitted|
        (= |0_src_STATIC_BEST_None_prefixLength|
           |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|))))
(assert (= |0_src_STATIC_IMPORT_~Interface_0~_choice|
   (and |0_src_STATIC_IMPORT_~Interface_0~_permitted|
        (= |0_src_STATIC_BEST_None_prefixLength|
           |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|))))
(assert (= |0_dest_CONNECTED_IMPORT_~Interface_1~_choice|
   (and |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
        (= |0_dest_OVERALL_BEST_None_prefixLength|
           |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|)
        (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (= |0_dest_CONNECTED_IMPORT_~Interface_4~_choice|
   (and |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
        (= |0_dest_OVERALL_BEST_None_prefixLength|
           |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|)
        (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (= |0_dest_CONNECTED_IMPORT_~Interface_3~_choice|
   (and |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|
        (= |0_dest_OVERALL_BEST_None_prefixLength|
           |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|)
        (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (= |0_dest_CONNECTED_IMPORT_~Interface_5~_choice|
   (and |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
        (= |0_dest_OVERALL_BEST_None_prefixLength|
           |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|)
        (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (let ((a!1 (and (= |0_src_OVERALL_BEST_None_adminDist| 0)
                (or (= |0_src_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_src_OVERALL_BEST_None_metric|))))))
(let ((a!2 (and (= |0_src_OVERALL_BEST_None_prefixLength|
                   |0_src_CONNECTED_BEST_None_prefixLength|)
                (or (not (<= 0 |0_src_OVERALL_BEST_None_adminDist|)) a!1))))
  (or (not |0_src_CONNECTED_BEST_None_permitted|)
      (not (<= |0_src_OVERALL_BEST_None_prefixLength|
               |0_src_CONNECTED_BEST_None_prefixLength|))
      a!2))))
(assert (let ((a!1 (and (= |0_src_OVERALL_BEST_None_adminDist| 1)
                (or (= |0_src_OVERALL_BEST_None_metric| 0)
                    (not (<= 0 |0_src_OVERALL_BEST_None_metric|))))))
(let ((a!2 (and (= |0_src_OVERALL_BEST_None_prefixLength|
                   |0_src_STATIC_BEST_None_prefixLength|)
                (or (not (<= 1 |0_src_OVERALL_BEST_None_adminDist|)) a!1))))
  (or (not |0_src_STATIC_BEST_None_permitted|)
      (not (<= |0_src_OVERALL_BEST_None_prefixLength|
               |0_src_STATIC_BEST_None_prefixLength|))
      a!2))))
(assert (= (or |0_src_CONNECTED_BEST_None_permitted| |0_src_STATIC_BEST_None_permitted|)
   |0_src_OVERALL_BEST_None_permitted|))
(assert (or (and |0_src_CONNECTED_BEST_None_permitted|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_CONNECTED_BEST_None_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 0)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b0))
    (and |0_src_STATIC_BEST_None_permitted|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_STATIC_BEST_None_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 1)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b1))
    (not (or |0_src_CONNECTED_BEST_None_permitted|
             |0_src_STATIC_BEST_None_permitted|))))
(assert (or |0_CONTROL-FORWARDING_src_~Interface_2~|
    (not (and (= |0_dst-ip| #x02000001)
              |0_src_CONNECTED_IMPORT_~Interface_2~_choice|
              (= |0_src_OVERALL_BEST_None_prefixLength|
                 |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|)
              (= |0_src_OVERALL_BEST_None_adminDist| 0)
              (= |0_src_OVERALL_BEST_None_metric| 0)
              (= |0_src_OVERALL_BEST_None_history| #b0)))))
(assert (or |0_CONTROL-FORWARDING_src_~Interface_0~|
    (not (and (= |0_dst-ip| #x01000001)
              |0_src_CONNECTED_IMPORT_~Interface_0~_choice|
              (= |0_src_OVERALL_BEST_None_prefixLength|
                 |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|)
              (= |0_src_OVERALL_BEST_None_adminDist| 0)
              (= |0_src_OVERALL_BEST_None_metric| 0)
              (= |0_src_OVERALL_BEST_None_history| #b0)))))
(assert (or |0_CONTROL-FORWARDING_src_~Interface_2~|
    (not (and |0_src_STATIC_IMPORT_~Interface_2~_choice|
              (= |0_src_OVERALL_BEST_None_prefixLength|
                 |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|)
              (= |0_src_OVERALL_BEST_None_adminDist| 1)
              (= |0_src_OVERALL_BEST_None_metric| 0)
              (= |0_src_OVERALL_BEST_None_history| #b1)))))
(assert (or |0_CONTROL-FORWARDING_src_~Interface_0~|
    (not (and |0_src_STATIC_IMPORT_~Interface_0~_choice|
              (= |0_src_OVERALL_BEST_None_prefixLength|
                 |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|)
              (= |0_src_OVERALL_BEST_None_adminDist| 1)
              (= |0_src_OVERALL_BEST_None_metric| 0)
              (= |0_src_OVERALL_BEST_None_history| #b1)))))
(assert (or (not |0_CONTROL-FORWARDING_src_~Interface_2~|)
    (and (= |0_dst-ip| #x02000001)
         |0_src_CONNECTED_IMPORT_~Interface_2~_choice|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 0)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b0))
    (and |0_src_STATIC_IMPORT_~Interface_2~_choice|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_STATIC_IMPORT_~Interface_2~_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 1)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b1))))
(assert (or (not |0_CONTROL-FORWARDING_src_~Interface_0~|)
    (and (= |0_dst-ip| #x01000001)
         |0_src_CONNECTED_IMPORT_~Interface_0~_choice|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 0)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b0))
    (and |0_src_STATIC_IMPORT_~Interface_0~_choice|
         (= |0_src_OVERALL_BEST_None_prefixLength|
            |0_src_STATIC_IMPORT_~Interface_0~_prefixLength|)
         (= |0_src_OVERALL_BEST_None_adminDist| 1)
         (= |0_src_OVERALL_BEST_None_metric| 0)
         (= |0_src_OVERALL_BEST_None_history| #b1))))
(assert (or |0_CONTROL-FORWARDING_dest_~Interface_1~|
    (not (and (= |0_dst-ip| #x01000000)
              |0_dest_CONNECTED_IMPORT_~Interface_1~_choice|
              (= |0_dest_OVERALL_BEST_None_prefixLength|
                 |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|)
              (= |0_dest_OVERALL_BEST_None_metric| 0)))))
(assert (let ((a!1 (not (and (not (= |0_dst-ip| #x01010000))
                     |0_dest_CONNECTED_IMPORT_~Interface_4~_choice|
                     (= |0_dest_OVERALL_BEST_None_prefixLength|
                        |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|)
                     (= |0_dest_OVERALL_BEST_None_metric| 0)))))
  (or |0_CONTROL-FORWARDING_dest_~Interface_4~| a!1)))
(assert (or |0_CONTROL-FORWARDING_dest_~Interface_3~|
    (not (and (= |0_dst-ip| #x02000000)
              |0_dest_CONNECTED_IMPORT_~Interface_3~_choice|
              (= |0_dest_OVERALL_BEST_None_prefixLength|
                 |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|)
              (= |0_dest_OVERALL_BEST_None_metric| 0)))))
(assert (let ((a!1 (not (and (not (= |0_dst-ip| #x02010000))
                     |0_dest_CONNECTED_IMPORT_~Interface_5~_choice|
                     (= |0_dest_OVERALL_BEST_None_prefixLength|
                        |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|)
                     (= |0_dest_OVERALL_BEST_None_metric| 0)))))
  (or |0_CONTROL-FORWARDING_dest_~Interface_5~| a!1)))
(assert (or (not |0_CONTROL-FORWARDING_dest_~Interface_5~|)
    (and (not (= |0_dst-ip| #x02010000))
         |0_dest_CONNECTED_IMPORT_~Interface_5~_choice|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (or (not |0_CONTROL-FORWARDING_dest_~Interface_1~|)
    (and (= |0_dst-ip| #x01000000)
         |0_dest_CONNECTED_IMPORT_~Interface_1~_choice|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (or (not |0_CONTROL-FORWARDING_dest_~Interface_4~|)
    (and (not (= |0_dst-ip| #x01010000))
         |0_dest_CONNECTED_IMPORT_~Interface_4~_choice|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (or (not |0_CONTROL-FORWARDING_dest_~Interface_3~|)
    (and (= |0_dst-ip| #x02000000)
         |0_dest_CONNECTED_IMPORT_~Interface_3~_choice|
         (= |0_dest_OVERALL_BEST_None_prefixLength|
            |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength|)
         (= |0_dest_OVERALL_BEST_None_metric| 0))))
(assert (= |0_CONTROL-FORWARDING_src_~Interface_2~|
   |0_DATA-FORWARDING_src_~Interface_2~|))
(assert (= |0_CONTROL-FORWARDING_src_~Interface_0~|
   |0_DATA-FORWARDING_src_~Interface_0~|))
(assert (= |0_CONTROL-FORWARDING_dest_~Interface_5~|
   |0_DATA-FORWARDING_dest_~Interface_5~|))
(assert (= |0_CONTROL-FORWARDING_dest_~Interface_1~|
   |0_DATA-FORWARDING_dest_~Interface_1~|))
(assert (= |0_CONTROL-FORWARDING_dest_~Interface_4~|
   |0_DATA-FORWARDING_dest_~Interface_4~|))
(assert (= |0_CONTROL-FORWARDING_dest_~Interface_3~|
   |0_DATA-FORWARDING_dest_~Interface_3~|))
(assert (or |0_src_OVERALL_BEST_None_permitted|
    (= |0_src_OVERALL_BEST_None_adminDist| 0)))
(assert (or |0_src_OVERALL_BEST_None_permitted|
    (= |0_src_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_src_OVERALL_BEST_None_permitted| (= |0_src_OVERALL_BEST_None_metric| 0)))
(assert (or |0_src_OVERALL_BEST_None_permitted|
    (= |0_src_OVERALL_BEST_None_history| #b0)))
(assert (or |0_src_CONNECTED_BEST_None_permitted|
    (= |0_src_CONNECTED_BEST_None_prefixLength| 0)))
(assert (or |0_src_STATIC_BEST_None_permitted|
    (= |0_src_STATIC_BEST_None_prefixLength| 0)))
(assert (or |0_dest_OVERALL_BEST_None_permitted|
    (= |0_dest_OVERALL_BEST_None_prefixLength| 0)))
(assert (or |0_dest_OVERALL_BEST_None_permitted|
    (= |0_dest_OVERALL_BEST_None_metric| 0)))
(assert true)
(assert (or |0_src_CONNECTED_IMPORT_~Interface_2~_permitted|
    (= |0_src_CONNECTED_IMPORT_~Interface_2~_prefixLength| 0)))
(assert (or |0_src_CONNECTED_IMPORT_~Interface_0~_permitted|
    (= |0_src_CONNECTED_IMPORT_~Interface_0~_prefixLength| 0)))
(assert (or |0_src_STATIC_IMPORT_~Interface_2~_permitted|
    (= |0_src_STATIC_IMPORT_~Interface_2~_prefixLength| 0)))
(assert (or |0_src_STATIC_IMPORT_~Interface_0~_permitted|
    (= |0_src_STATIC_IMPORT_~Interface_0~_prefixLength| 0)))
(assert (or |0_dest_CONNECTED_IMPORT_~Interface_5~_permitted|
    (= |0_dest_CONNECTED_IMPORT_~Interface_5~_prefixLength| 0)))
(assert (or |0_dest_CONNECTED_IMPORT_~Interface_1~_permitted|
    (= |0_dest_CONNECTED_IMPORT_~Interface_1~_prefixLength| 0)))
(assert (or |0_dest_CONNECTED_IMPORT_~Interface_4~_permitted|
    (= |0_dest_CONNECTED_IMPORT_~Interface_4~_prefixLength| 0)))
(assert (or |0_dest_CONNECTED_IMPORT_~Interface_3~_permitted|
    (= |0_dest_CONNECTED_IMPORT_~Interface_3~_prefixLength| 0)))
(assert (or (= |0_dst-ip| #x02000001)
    (= |0_dst-ip| #x01000001)
    (= |0_dst-ip| #x01010000)
    (= |0_dst-ip| #x02010000)))
(assert (= |0__reachable_src| (not (<= |0__reachable-id_src| 0))))
(assert (>= |0__reachable-id_src| 0))
(assert (= |0__reachable_dest| (not (<= |0__reachable-id_dest| 0))))
(assert (>= |0__reachable-id_dest| 0))
(assert (let ((a!1 (or (and |0_DATA-FORWARDING_src_~Interface_2~|
                    (not (<= |0__reachable-id_dest| 0)))
               (and |0_DATA-FORWARDING_src_~Interface_0~|
                    (not (<= |0__reachable-id_dest| 0)))))
      (a!2 (not (and |0_DATA-FORWARDING_src_~Interface_2~|
                     (not (<= |0__reachable-id_dest| 0)))))
      (a!3 (not (and |0_DATA-FORWARDING_src_~Interface_0~|
                     (not (<= |0__reachable-id_dest| 0))))))
(let ((a!4 (and (or (not (<= |0__reachable-id_src| |0__reachable-id_dest|)) a!2)
                (or (not (<= |0__reachable-id_src| |0__reachable-id_dest|)) a!3))))
  (ite a!1 a!4 (= |0__reachable-id_src| 0)))))
(assert (let ((a!1 (or (and |0_DATA-FORWARDING_dest_~Interface_1~|
                    (not (<= |0__reachable-id_src| 0)))
               (and |0_DATA-FORWARDING_dest_~Interface_3~|
                    (not (<= |0__reachable-id_src| 0)))))
      (a!2 (not (and |0_DATA-FORWARDING_dest_~Interface_1~|
                     (not (<= |0__reachable-id_src| 0)))))
      (a!3 (not (and |0_DATA-FORWARDING_dest_~Interface_3~|
                     (not (<= |0__reachable-id_src| 0))))))
(let ((a!4 (and (or (not (<= |0__reachable-id_dest| |0__reachable-id_src|)) a!2)
                (or (not (<= |0__reachable-id_dest| |0__reachable-id_src|)) a!3))))
  (ite (or |0_DATA-FORWARDING_dest_~Interface_5~|
           |0_DATA-FORWARDING_dest_~Interface_4~|
           (and |0_dest_OVERALL_BEST_None_permitted| (= |0_dst-ip| #x02010000))
           (and |0_dest_OVERALL_BEST_None_permitted| (= |0_dst-ip| #x01000001))
           (and |0_dest_OVERALL_BEST_None_permitted| (= |0_dst-ip| #x01010000))
           (and |0_dest_OVERALL_BEST_None_permitted| (= |0_dst-ip| #x02000001)))
       (= |0__reachable-id_dest| 1)
       (ite a!1 a!4 (= |0__reachable-id_dest| 0))))))
(assert (not |0__reachable_src|))
(assert (= |0_FAILED-EDGE_dest_~Interface_5~| 0))
(assert (or (not (= ((_ extract 31 1) |0_dst-ip|) #b0000000100000000000000000000000))
    (= |0_FAILED-EDGE_dest_src| 0)))
(assert (= |0_FAILED-EDGE_dest_~Interface_4~| 0))
(assert (or (not (= ((_ extract 31 1) |0_dst-ip|) #b0000001000000000000000000000000))
    (= |0_FAILED-EDGE_dest_src| 0)))

(check-sat)
(get-model)
