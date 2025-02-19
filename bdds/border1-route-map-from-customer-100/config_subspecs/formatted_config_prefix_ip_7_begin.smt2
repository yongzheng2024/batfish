(declare-fun match_prefix_ip_4 () Int)
(declare-fun match_prefix_ip_9 () Int)
(declare-fun config_prefix_ip_7_begin () Int)
(declare-fun match_prefix_ip_14 () Int)
(assert 
    (= 
        (ite 
            (and 
                (>= match_prefix_ip_14 167772160)
                (<= match_prefix_ip_14 184549375)
                (>= match_prefix_length_15 8)
                (<= match_prefix_length_15 32)
            )
            true
            (ite 
                (and 
                    (>= match_prefix_ip_9 config_prefix_ip_7_begin)
                    (<= match_prefix_ip_9 2887778303)
                    (>= match_prefix_length_10 12)
                    (<= match_prefix_length_10 32)
                )
                true
                (ite 
                    (and 
                        (>= match_prefix_ip_4 3232235520)
                        (<= match_prefix_ip_4 3232301055)
                        (>= match_prefix_length_5 16)
                        (<= match_prefix_length_5 32)
                    )
                    true
                    false
                )
            )
        )
        false
    )
)
(assert 
    (= config_prefix_ip_7_begin 2886729728)
)
(assert 
    (or 
        (and 
            (>= match_prefix_ip_4 167772160)
            (<= match_prefix_ip_4 184549375)
            (>= match_prefix_length_5 8)
            (<= match_prefix_length_5 32)
        )
        (and 
            (>= match_prefix_ip_4 2886729728)
            (<= match_prefix_ip_4 2887778303)
            (>= match_prefix_length_5 12)
            (<= match_prefix_length_5 32)
        )
        (and 
            (>= match_prefix_ip_4 3232235520)
            (<= match_prefix_ip_4 3232301055)
            (>= match_prefix_length_5 16)
            (<= match_prefix_length_5 32)
        )
    )
)
(assert 
    (= match_prefix_ip_4 match_prefix_ip_9)
)
(assert 
    (= match_prefix_ip_4 match_prefix_ip_14)
)
(check-sat)
(get-model)
