(declare-fun config_prefix_ip_2_begin () Int)
(assert (= (ite (and (>= match_prefix_ip_14 167772160) (<= match_prefix_ip_14 184549375) (>= match_prefix_length_15 8) (<= match_prefix_length_15 32)) true (ite (and (>= match_prefix_ip_9 2886729728) (<= match_prefix_ip_9 2887778303) (>= match_prefix_length_10 12) (<= match_prefix_length_10 32)) true (ite (and (>= match_prefix_ip_4 config_prefix_ip_2_begin) (<= match_prefix_ip_4 3232301055) (>= match_prefix_length_5 16) (<= match_prefix_length_5 32)) true false))) false))
(check-sat)
(get-model)
