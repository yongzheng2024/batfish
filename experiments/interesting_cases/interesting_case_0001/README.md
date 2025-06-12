The directory test\_example contains a network topology as shown in below.

```txt
    +--------+          +--------+                              +---------+
    |  ISP1  |----------|   R1   |-----+                   +----|Customer1|
    +--------+     +----+--------+     |                   |    +---------+
                   |         |         |                   |
                   |         |         |                   |
    +--------+-----+    +--------+     +----+--------+-----+    +---------+
    |  ISP2  |----------|   R2   |----------|   R3   |----------|Customer2|
    +--------+          +--------+          +--------+          +---------+
```

AS100: R1, R2 and R3
AS200: ISP1
AS300: ISP2
AS400: Customer1
AS500: Customer2

In R1, routes from ISP1 are configured local-preference to 400, routes from ISP2 are configured local-preference to 350.
In R2, routes from ISP2 are configured local-preference to 350.
The higher local-preference represents higher priority for routes, and the local-preference attribute will continuously propagate within the AS.

So, when same prefix routes from ISP1 and ISP2 both propagate to R3, R3 will select routes from ISP1, and propagate this best route to Customer1 and Customer2.

But, I find some interesting cases that are as follows.

When I check reachability from Customer2 to ISP1 (192.0.2.0/24), the result (can reachable) is expected.
But, when i check reachability from Customer2 to ISP2 (192.0.2.0/24), the result (can reachable) is error. In this case, the expected result is can not reachable, because the routes (192.0.2.0/24) from ISP2 is not best route for R3.

And, when I use the check\_key\_variables.py script to filter key varabiles for these two cases, the first case is expected that the script filter some key variables (to-propagated network, route-map, local-preference, etc.). But, the second case is error maybe that the script just filter some key variables about to-propagated network in ISP2.

The directory smt\_output\_0001 contains the smt encoding and corresponding files of the first case.
The directory smt\_output\_0002 contains these files of the second case.
