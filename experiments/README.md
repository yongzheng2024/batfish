Network Setup
-------------

```txt
  +----------+                   +------------+                   +------------+
  |          | GE1/0       GE0/0 |            | GE1/0       GE0/0 |            |
  | as1core1 |-------------------| as1border1 |-------------------| as2border1 |
  |          |   OSPF/iBGP peer  |            |      eBGP peer    |            |
  +----------+                   +------------+                   +------------+
```

Here the goal is to verify that `as2border1` can reach `as1core1 GE1/0`.

Encoding files
--------------

1. The encoding for verification is located 
    [here](reachability_smt_output_0001/smt_encoding.smt2).

    This is UNSAT, as it is a verification problem, where the network model
    is conjuncted with a negated property. UNSAT means that for all possible 
    external route announcement, the routers will always satisfy the specified
    reachability.

    We modified Minesweeper such that the underlying encoding contains explicit
    symbolic variables for each configuration fields.  The mapping from config
    fields to the SMT variable is 
[here](reachability_smt_output_0001/configs_to_variables.txt).
    The modified encoding is checked equivalent to the original encoding,
    using Z3.

2. The list of interesting variables are
   [here](reachability_smt_output_0001/key_variables.txt).

   How they connect with the global property and what are their expected
   subspec, is explained in the following.

   (We validate their relevance by removing their constraints and got a SAT
    result from Z3. That is, removing their constraints leads to a failed
    verification.)

How does the network work
--------------------------

The partical key configuration of `as1border1` is following.

```txt
!
! define interface and relevant network address
interface Loopback0
 ip address 1.1.1.1 255.255.255.255
!
interface GigabitEthernet1/0
 ip address 10.12.11.1 255.255.255.0
 negotiation auto
!
! define bgp basic configuration (as-number, router-id, bgp peer)
router bgp 1
 bgp router-id 1.1.1.1
 neighbor as2 peer-group
 neighbor as2 remote-as 2
 neighbor 10.12.11.2 peer-group as2
 !
 ! define bgp to-propagate network address, and bgp peer route-map
 address-family ipv4
  network 1.0.1.0 mask 255.255.255.0
  network 1.0.2.0 mask 255.255.255.0
  neighbor as2 send-community
  neighbor as2 route-map as2_to_as1 in
  neighbor 10.12.11.2 activate
 exit-address-family
!
! define route-map configuration and denpendcies configuration
access-list 101 permit ip host 1.0.1.0 host 255.255.255.0
access-list 101 permit ip host 1.0.2.0 host 255.255.255.0
!
route-map as1_to_as2 permit 1
 match ip address 101
 set metric 50
 set community 1:2 additive
```

The partical key configuration of `as2border1` is following.

```txt
!
! define interface and relevant network address
interface Loopback0
 ip address 2.1.1.1 255.255.255.255
!
interface GigabitEthernet0/0
 ip address 10.12.11.2 255.255.255.0
 ! ip access-group OUTSIDE_TO_INSIDE in
 ! ip access-group INSIDE_TO_AS1 out
 media-type gbic
 speed 1000
 duplex full
 negotiation auto
!
! define bgp basic configuration (as-number, router-id, bgp peer)
router bgp 2
 bgp router-id 2.1.1.1
 neighbor as1 peer-group
 neighbor as1 remote-as 1
 neighbor 10.12.11.1 peer-group as1
 !
 ! define bgp peer route-map
 address-family ipv4
  neighbor as1 send-community
  neighbor as1 route-map as1_to_as2 in
  neighbor as1 route-map as2_to_as1 out
 exit-address-family
!
! define route-map configuration and denpendcies configuration (partical)
access-list 101 permit ip host 1.0.1.0 host 255.255.255.0
access-list 101 permit ip host 1.0.2.0 host 255.255.255.0
!
route-map as1_to_as2 permit 100
 match ip address 101
 set local-preference 350
 set community 1:2 additive
```


1. For reachability property `as2border1 -> as1core GE1/0 (i.e. 1.0.1.1/24)`,
   as1border1 must propagate route prefix that include the target address
   `1.0.1.0/24` to as2border1.

    In other words, the subspec for these three variable should establish the notion 
    that network IP (`Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__ip`), 
    network mask (`Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__mask`) 
    should include the target address (1.0.1.1 255.255.255.0) and start of 
    the corredponding network prefix range 
    (`Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__prefix_range_start`) 
    should be fewer than 24.

```txt
// as1border1 configuration: network 1.0.1.0 mask 255.255.255.0
// Config_...__1_0_1_0__ip = BitVecExpr(..., 0b0010000000100000, 32)
// Config_...__1_0_1_0__mask = BitVecExpr(..., 0b1111111111110000, 32)
// Config_...__1_0_1_0__prefix_range_start = ArithExpr(..., 24), 
// prefix_range_start according to mask 255.255.255.0 that match the first 24 bit
Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__ip
Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__mask
Config_as1border1_RoutingPolicy_BGP_COMMON_EXPORT_POLICY_default__Line1__1_0_1_0__prefix_range_start
```

2. The above route to the desination should not be blocked by any route-map
    filter. For instance, consider the following route-map for at router
    `as1borader1`:

    Here `Config_as1border1_RouteFilterList_101__1_0_1_0__action` should always be `permit`.
    Network IP (`Config_as1border1_RouteFilterList_101__1_0_1_0__ip`), 
    network mask (`Config_as1border1_RouteFilterList_101__1_0_1_0__mask`) 
    should include the target address (1.0.1.1 255.255.255.0).
    `Config_as1border1_RouteFilterList_101__1_0_1_0__prefix_range_start` should also be fewer than 24, 
    such that it can match against the route to the desination (i.e. 1.0.1.1/24).

```txt
// as1border1 configuration: access-list 101 permit ip host 1.0.1.0 host 255.255.255.0
// Config_...__1_0_1_0__action = BoolExpr(..., true) (i.e. permit)
// Config_...__1_0_1_0__ip = BitVecExpr(..., 0b0010000000100000, 32)
// Config_...__1_0_1_0__mask = BitVecExpr(..., 0b1111111111110000, 32)
// Config_...__1_0_1_0__prefix_range_start = ArithExpr(..., 24)
Config_as1border1_RouteFilterList_101__1_0_1_0__action
Config_as1border1_RouteFilterList_101__1_0_1_0__ip
Config_as1border1_RouteFilterList_101__1_0_1_0__mask
Config_as1border1_RouteFilterList_101__1_0_1_0__prefix_range_start

```

3. Similarly, this route should not be blocked by the import filter at 
    `as2border1`:

    Here `Config_as2border1_RouteFilterList_101__1_0_1_0__action` should always be `permit`. 
    Network IP (`Config_as2border1_RouteFilterList_101__1_0_1_0__ip`), 
    network mask (`Config_as2border1_RouteFilterList_101__1_0_1_0__mask`) 
    should include the target address (1.0.1.1 255.255.255.0).
    `Config_as2border1_RouteFilterList_101__1_0_1_0__prefix_range_start` should also be fewer than 24, 
    such that it can match against the route to the desination (i.e. 1.0.1.0/24).

```
// as2border1 configuration: access-list 101 permit ip host 1.0.1.0 host 255.255.255.0
// Config_...__1_0_1_0__action = BoolExpr(..., true) (i.e. permit)
// Config_...__1_0_1_0__ip = BitVecExpr(..., 0b0010000000100000, 32)
// Config_...__1_0_1_0__mask = BitVecExpr(..., 0b1111111111110000, 32)
// Config_...__1_0_1_0__prefix_range_start = ArithExpr(..., 24)
Config_as2border1_RouteFilterList_101__1_0_1_0__action
Config_as2border1_RouteFilterList_101__1_0_1_0__ip
Config_as2border1_RouteFilterList_101__1_0_1_0__mask
Config_as2border1_RouteFilterList_101__1_0_1_0__prefix_range_start
```
