(declare-fun config_action_permit_6 () Bool)
(declare-fun config_prefix_length_3 () Int)
(declare-fun match_prefix_length_5 () Int)
(declare-fun config_prefix_ip_2_end () Int)
(declare-fun match_prefix_ip_4 () Int)
(declare-fun config_prefix_ip_2_begin () Int)
(declare-fun config_action_permit_11 () Bool)
(declare-fun config_prefix_length_8_end () Int)
(declare-fun match_prefix_length_10 () Int)
(declare-fun config_prefix_length_8_begin () Int)
(declare-fun config_prefix_ip_7_end () Int)
(declare-fun match_prefix_ip_9 () Int)
(declare-fun config_prefix_ip_7_begin () Int)
(declare-fun config_action_permit_16 () Bool)
(declare-fun config_prefix_length_13_end () Int)
(declare-fun match_prefix_length_15 () Int)
(declare-fun config_prefix_length_13_begin () Int)
(declare-fun config_prefix_ip_12_end () Int)
(declare-fun match_prefix_ip_14 () Int)
(declare-fun config_prefix_ip_12_begin () Int)

; symbolic route path smt expression
; !
; ip prefix-list private-ips seq 5 permit 10.0.0.0/8 ge 8
; ip prefix-list private-ips seq 10 permit 172.16.0.0/12 ge 12
; ip prefix-list private-ips seq 15 permit 192.168.0.0/16
; !
; route-map from_customer deny 100
;  match ip address prefix-list private-ips
(assert (let ((a!1 (ite (and ; (= config_prefix_ip_7_begin 2886729728)
                        ; (= config_prefix_ip_7_end 2887778303)
                        (>= match_prefix_ip_9 config_prefix_ip_7_begin)
                        (<= match_prefix_ip_9 config_prefix_ip_7_end)
                        ; (= config_prefix_length_8_begin 12)
                        ; (= config_prefix_length_8_end 32)
                        (>= match_prefix_length_10 config_prefix_length_8_begin)
                        (<= match_prefix_length_10 config_prefix_length_8_end))
                     config_action_permit_11
                     (ite (and ; (= config_prefix_ip_2_begin 3232235520)
                          ; (= config_prefix_ip_2_end 3232301055)
                          (>= match_prefix_ip_4 config_prefix_ip_2_begin)
                          (<= match_prefix_ip_4 config_prefix_ip_2_end)
                          ; (= config_prefix_length_3 16)
                          ; scenario 1: match single prefix length
                          (= match_prefix_length_5 config_prefix_length_3))
                          ; scenario 2: match prefix length range
                          ; (>= match_prefix_length_5 config_prefix_length_3)
                          ; (<= match_prefix_length_5 config_prefix_length_3))
                       config_action_permit_6
                       false))))
(let ((a!2 (and true
                (ite (and ; (= config_prefix_ip_12_begin 167772160)
                          ; (= config_prefix_ip_12_end 184549375)
                          (>= match_prefix_ip_14 config_prefix_ip_12_begin)
                          (<= match_prefix_ip_14 config_prefix_ip_12_end)
                          ; (= config_prefix_length_13_begin 8)
                          ; (= config_prefix_length_13_end 32)
                          (>= match_prefix_length_15 config_prefix_length_13_begin)
                          (<= match_prefix_length_15 config_prefix_length_13_end))
                  config_action_permit_16
                  a!1))))
  ; (= a!2 true))))
  (= a!2 false))))

; configuration constraints
(assert (= config_prefix_ip_7_begin 2886729728))  ; 172.16.0.0
(assert (= config_prefix_ip_7_end 2887778303))    ; 172.31.255.255
(assert (= config_prefix_length_8_begin 12))
(assert (= config_prefix_length_8_end 32))
(assert (= config_action_permit_11 true))         ; permit (true) / deny (false)
(assert (= config_prefix_ip_2_begin 3232235520))  ; 192.168.0.0
(assert (= config_prefix_ip_2_end 3232301055))    ; 192.168.255.255
(assert (= config_prefix_length_3 16))
(assert (= config_action_permit_6 true))
(assert (= config_prefix_ip_12_begin 167772160))  ; 10.0.0.0
(assert (= config_prefix_ip_12_end 184549375))    ; 10.255.255.255
(assert (= config_prefix_length_13_begin 8))
(assert (= config_prefix_length_13_end 32))
(assert (= config_action_permit_16 true))

; partial input/output constraints
(assert
   (or
        (and (>= match_prefix_ip_4 167772160) (<= match_prefix_ip_4 184549375)
             (>= match_prefix_length_5 8) (<= match_prefix_length_5 32))
        (and (>= match_prefix_ip_4 2886729728) (<= match_prefix_ip_4 2887778303)
             (>= match_prefix_length_5 12) (<= match_prefix_length_5 32))
        (and (>= match_prefix_ip_4 3232235520) (<= match_prefix_ip_4 3232301055)
             (>= match_prefix_length_5 16) (<= match_prefix_length_5 32))
   )
)

(assert (= match_prefix_ip_4 match_prefix_ip_9))
(assert (= match_prefix_ip_4 match_prefix_ip_14))
(assert (= match_prefix_length_5 match_prefix_length_10))
(assert (= match_prefix_length_5 match_prefix_length_15))


(check-sat)
(get-model)
