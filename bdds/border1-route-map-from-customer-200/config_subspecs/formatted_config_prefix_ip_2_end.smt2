(declare-fun config_prefix_ip_2_end () Int)
(declare-fun match_prefix_ip_4 () Int)
(declare-fun match_prefix_ip_9 () Int)
(declare-fun match_prefix_ip_14 () Int)
(assert 
    (= 
        (and 
            (not 
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
                            (>= match_prefix_ip_9 2886729728)
                            (<= match_prefix_ip_9 2887778303)
                            (>= match_prefix_length_10 12)
                            (<= match_prefix_length_10 32)
                        )
                        true
                        (ite 
                            (and 
                                (>= match_prefix_ip_4 3232235520)
                                (<= match_prefix_ip_4 config_prefix_ip_2_end)
                                (>= match_prefix_length_5 16)
                                (<= match_prefix_length_5 32)
                            )
                            true
                            false
                        )
                    )
                )
            )
            (ite 
                (and 
                    (>= match_prefix_ip_26 84215040)
                    (<= match_prefix_ip_26 84215295)
                    (>= match_prefix_length_27 24)
                    (<= match_prefix_length_27 32)
                )
                true
                false
            )
        a!3)
        true
    )
)
(assert 
    (= config_prefix_ip_2_end 3232301055)
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
