(declare-fun config_prefix_ip_24_end () Int)
(declare-fun match_prefix_ip_26 () Int)

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
                                (<= match_prefix_ip_4 3232301055) 
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
                    (<= match_prefix_ip_26 config_prefix_ip_24_end) 
                    (>= match_prefix_length_27 24) 
                    (<= match_prefix_length_27 32)
                ) 
                true 
                false
            ) 
            a!3
        ) 
        true
    )
)

; (assert (= config_prefix_ip_24_end 84215295))

(check-sat)
(get-model)
