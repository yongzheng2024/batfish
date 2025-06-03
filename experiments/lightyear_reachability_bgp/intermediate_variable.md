#### PropertyAdder.java Line 68

```java
private void initializeReachabilityVars(
    EncoderSlice slice,
    Context ctx,
    Solver solver,
    Map<String, BoolExpr> reachableVars,
    Map<String, ArithExpr> idVars) {
  String sliceName = slice.getSliceName();
  ArithExpr zero = ctx.mkInt(0);
  for (String r : _encoderSlice.getGraph().getRouters()) {
    int id = _encoderSlice.getEncoder().getId();
    String s1 = id + "_" + sliceName + "_reachable-id_" + r;
    String s2 = id + "_" + sliceName + "_reachable_" + r;
    ArithExpr idVar = ctx.mkIntConst(s1);     // reachable-id Var
    BoolExpr var = ctx.mkBoolConst(s2);       // reachable Vakkkr
    idVars.put(r, idVar);
    reachableVars.put(r, var);
    _encoderSlice.getAllVariables().put(idVar.toString(), idVar);
    _encoderSlice.getAllVariables().put(var.toString(), var);
    // (= var (> idVar, 0))  ->  idVar = 0, ReachableVar = False
    // (>= idVar, 0)         ->  idVar > 0, ReachalceVar = True
    // -------------------------------------------------------------
    solver.add(ctx.mkEq(var, ctx.mkGt(idVar, zero)));
    // -------------------------------------------------------------
    solver.add(ctx.mkGe(idVar, zero));
  }
}
```

```smt
|0_SLICE-r2__reachable_r2|:
(assert (= |0_SLICE-r2__reachable_r2| (not (<= |0_SLICE-r2__reachable-id_r2| 0))))  Y
(assert (= |0_SLICE-r2__reachable_r2| (not (<= |0_SLICE-r2__reachable-id_r2| 0))))  Y
|0_SLICE-r2__reachable_r3|:
(assert (= |0_SLICE-r2__reachable_r3| (not (<= |0_SLICE-r2__reachable-id_r3| 0))))  Y
(assert (= |0_SLICE-r2__reachable_r3| (not (<= |0_SLICE-r2__reachable-id_r3| 0))))  Y
|0_SLICE-r2__reachable_r1|:
(assert (= |0_SLICE-r2__reachable_r1| (not (<= |0_SLICE-r2__reachable-id_r1| 0))))  Y
(assert (= |0_SLICE-r2__reachable_r1| (not (<= |0_SLICE-r2__reachable-id_r1| 0))))  Y

|0_SLICE-r1__reachable_r2|:
(assert (= |0_SLICE-r1__reachable_r2| (not (<= |0_SLICE-r1__reachable-id_r2| 0))))  Y
(assert (= |0_SLICE-r1__reachable_r2| (not (<= |0_SLICE-r1__reachable-id_r2| 0))))  Y
|0_SLICE-r1__reachable_r3|:
(assert (= |0_SLICE-r1__reachable_r3| (not (<= |0_SLICE-r1__reachable-id_r3| 0))))  Y
(assert (= |0_SLICE-r1__reachable_r3| (not (<= |0_SLICE-r1__reachable-id_r3| 0))))  Y
|0_SLICE-r1__reachable_r1|:
(assert (= |0_SLICE-r1__reachable_r1| (not (<= |0_SLICE-r1__reachable-id_r1| 0))))  Y
(assert (= |0_SLICE-r1__reachable_r1| (not (<= |0_SLICE-r1__reachable-id_r1| 0))))  Y

|0_SLICE-r3__reachable_r2|:
(assert (= |0_SLICE-r3__reachable_r2| (not (<= |0_SLICE-r3__reachable-id_r2| 0))))  Y
(assert (= |0_SLICE-r3__reachable_r2| (not (<= |0_SLICE-r3__reachable-id_r2| 0))))  Y
|0_SLICE-r3__reachable_r3|:
(assert (= |0_SLICE-r3__reachable_r3| (not (<= |0_SLICE-r3__reachable-id_r3| 0))))  Y
(assert (= |0_SLICE-r3__reachable_r3| (not (<= |0_SLICE-r3__reachable-id_r3| 0))))  Y
|0_SLICE-r3__reachable_r1|:
(assert (= |0_SLICE-r3__reachable_r1| (not (<= |0_SLICE-r3__reachable-id_r1| 0))))  Y
(assert (= |0_SLICE-r3__reachable_r1| (not (<= |0_SLICE-r3__reachable-id_r1| 0))))  Y

|0_SLICE-MAIN__reachable_r2|:
(assert (= |0_SLICE-MAIN__reachable_r2| (not (<= |0_SLICE-MAIN__reachable-id_r2| 0))))  Y
|0_SLICE-MAIN__reachable_r3|:
(assert (= |0_SLICE-MAIN__reachable_r3| (not (<= |0_SLICE-MAIN__reachable-id_r3| 0))))  Y
|0_SLICE-MAIN__reachable_isp1|:
(assert (= |0_SLICE-MAIN__reachable_isp1| (not (<= |0_SLICE-MAIN__reachable-id_isp1| 0))))  Y
|0_SLICE-MAIN__reachable_isp2|:
(assert (= |0_SLICE-MAIN__reachable_isp2| (not (<= |0_SLICE-MAIN__reachable-id_isp2| 0))))  Y
|0_SLICE-MAIN__reachable_customer|:
(assert (= |0_SLICE-MAIN__reachable_customer| (not (<= |0_SLICE-MAIN__reachable-id_customer| 0))))  Y
|0_SLICE-MAIN__reachable_r1|:
(assert (= |0_SLICE-MAIN__reachable_r1| (not (<= |0_SLICE-MAIN__reachable-id_r1| 0))))  Y
```

==========================================================================================

#### PropertyAdder.java Line 191

```java
Map<String, BoolExpr> instrumentReachability(String router) {
  @SuppressWarnings("PMD.CloseResource")
  Context ctx = _encoderSlice.getCtx();
  Solver solver = _encoderSlice.getSolver();
  Map<String, BoolExpr> reachableVars = new HashMap<>();
  Map<String, ArithExpr> idVars = new HashMap<>();
  initializeReachabilityVars(_encoderSlice, ctx, solver, reachableVars, idVars);

  ArithExpr baseId = idVars.get(router);
  // -----------------------------------------------------------------
  _encoderSlice.add(ctx.mkEq(baseId, ctx.mkInt(1)));
  // -----------------------------------------------------------------

  Graph g = _encoderSlice.getGraph();
  for (Entry<String, List<GraphEdge>> entry : g.getEdgeMap().entrySet()) {
    String r = entry.getKey();
    List<GraphEdge> edges = entry.getValue();
    if (!r.equals(router)) {
      ArithExpr id = idVars.get(r);
      BoolExpr cond = recursiveReachability(ctx, _encoderSlice, edges, idVars, r, id);
      solver.add(cond);
    }
  }

  return reachableVars;
}
```

```smt
|0_SLICE-r2__reachable-id_r2|:
(assert (= |0_SLICE-r2__reachable-id_r2| 1))  Y
(assert (= |0_SLICE-r2__reachable-id_r2| 1))  Y
|0_SLICE-r1__reachable-id_r1|:
(assert (= |0_SLICE-r1__reachable-id_r1| 1))  Y
(assert (= |0_SLICE-r1__reachable-id_r1| 1))  Y
|0_SLICE-r3__reachable-id_r3|:
(assert (= |0_SLICE-r3__reachable-id_r3| 1))  Y
(assert (= |0_SLICE-r3__reachable-id_r3| 1))  Y
```

=========================================================================================

#### EncodingId_FAILED-EDGE_RouterName_PeerName

```java
// k: user-specificed the limit number of edge (or node) failure (default: k = 0)
// vars: the variables of all non-specificed not-failed edges (or nodes)
private void addFailedConstraints(int k, Set<ArithExpr> vars) {
  ArithExpr sum = mkInt(0);
  for (ArithExpr var : vars) {
    sum = mkSum(sum, var);
    add(mkGe(var, mkInt(0)));
    add(mkLe(var, mkInt(1)));
  }
  if (k == 0) {
    for (ArithExpr var : vars) {
      // -------------------------------------------------------------
      add(mkEq(var, mkInt(0)));
      // -------------------------------------------------------------
    }
  } else {
    add(mkLe(sum, mkInt(k)));
  }
}
```

```smt
|0_FAILED-EDGE_r2_r3|:
(assert (= |0_FAILED-EDGE_r2_r3| 0))  Y
|0_FAILED-EDGE_r1_r3|:
(assert (= |0_FAILED-EDGE_r1_r3| 0))  Y
|0_FAILED-EDGE_customer_r3|:
(assert (= |0_FAILED-EDGE_customer_r3| 0))  Y
|0_FAILED-EDGE_isp2_r2|:
(assert (= |0_FAILED-EDGE_isp2_r2| 0))  Y
|0_FAILED-EDGE_r2_Loopback0|:
(assert (= |0_FAILED-EDGE_r2_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_r2_Loopback0| 0))  Y
|0_FAILED-EDGE_r1_Loopback0|:
(assert (= |0_FAILED-EDGE_r1_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_r1_Loopback0| 0))  Y
|0_FAILED-EDGE_customer_Loopback0|:
(assert (= |0_FAILED-EDGE_customer_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_customer_Loopback0| 0))
|0_FAILED-EDGE_r3_Loopback0|:
(assert (= |0_FAILED-EDGE_r3_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_r3_Loopback0| 0))
|0_FAILED-EDGE_isp1_GigabitEthernet1/0|:
(assert (= |0_FAILED-EDGE_isp1_GigabitEthernet1/0| 0))  Y
(assert (= |0_FAILED-EDGE_isp1_GigabitEthernet1/0| 0))
|0_FAILED-EDGE_isp1_Loopback0|:
(assert (= |0_FAILED-EDGE_isp1_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_isp1_Loopback0| 0))
|0_FAILED-EDGE_isp2_Loopback0|:
(assert (= |0_FAILED-EDGE_isp2_Loopback0| 0))  Y
(assert (= |0_FAILED-EDGE_isp2_Loopback0| 0))
|0_FAILED-EDGE_customer_GigabitEthernet1/0|:
(assert (= |0_FAILED-EDGE_customer_GigabitEthernet1/0| 0))  Y
(assert (= |0_FAILED-EDGE_customer_GigabitEthernet1/0| 0))
|0_FAILED-EDGE_r1_r2|:
(assert (= |0_FAILED-EDGE_r1_r2| 0))  Y
|0_FAILED-EDGE_isp1_r1|:
(assert (= |0_FAILED-EDGE_isp1_r1| 0))  Y
|0_FAILED-EDGE_isp2_GigabitEthernet1/0|:
(assert (= |0_FAILED-EDGE_isp2_GigabitEthernet1/0| 0))  Y
(assert (= |0_FAILED-EDGE_isp2_GigabitEthernet1/0| 0))

|0_FAILED-NODE_isp1|:
(assert (= |0_FAILED-NODE_isp1| 0))  Y
|0_FAILED-NODE_isp2|:
(assert (= |0_FAILED-NODE_isp2| 0))  Y
|0_FAILED-NODE_customer|:
(assert (= |0_FAILED-NODE_customer| 0))  Y
|0_FAILED-NODE_r3|:
(assert (= |0_FAILED-NODE_r3| 0))  Y
|0_FAILED-NODE_r1|:
(assert (= |0_FAILED-NODE_r1| 0))  Y
|0_FAILED-NODE_r2|:
(assert (= |0_FAILED-NODE_r2| 0))  Y
```

==========================================================================================

#### EncoderSlice.java Line 1061

```java
private void addCommunityConstraints() {
  for (SymbolicRoute r : getAllSymbolicRecords()) {
    for (Entry<CommunityVar, BoolExpr> entry : r.getCommunities().entrySet()) {
      CommunityVar cvar = entry.getKey();
      BoolExpr e = entry.getValue();

      if (cvar.getType() == CommunityVar.Type.REGEX) {
        BoolExpr acc = mkFalse();
        List<CommunityVar> deps = getGraph().getCommunityDependencies().get(cvar);
        for (CommunityVar dep : deps) {
          BoolExpr depExpr = r.getCommunities().get(dep);
          acc = mkOr(acc, depExpr);
        }
        // -----------------------------------------------------------
        BoolExpr regex = mkEq(acc, e);
        // -----------------------------------------------------------
        add(regex);
      }
    }
  }
}
```

```smt
|0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_100:1| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_community_100:1| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet3/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet3/0_community_100:1| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet3/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet3/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r3_community_100:1| |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_100:1| |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r2_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_100:1| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet2/0_community_100:1| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_community_100:1| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r2_community_100:1| |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_100:1| |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r3_BGP_EXPORT_iBGP-r1_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_100:1| |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_isp1_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_100:1| |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_isp2_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_customer_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_customer_BGP_SINGLE-EXPORT__community_100:1| |0_SLICE-MAIN_customer_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_customer_BGP_SINGLE-EXPORT__community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_100:1| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet2/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_100:1| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_100:1| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_100:1| |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r2_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
|0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:|:
(assert (= (or |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_100:1| |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:_OTHER|) |0_SLICE-MAIN_r1_BGP_EXPORT_iBGP-r3_community_(,\|\\{\|\\}\|^\|$\| )100:|))  Y
```
==========================================================================================

#### EncoderSlice.java Line 1609

```java
private void addBestPerProtocolConstraints() {
  for (Entry<String, Configuration> entry : getGraph().getConfigurations().entrySet()) {
    String router = entry.getKey();
    Configuration conf = entry.getValue();

    for (Protocol proto : getProtocols().get(router)) {
      SymbolicRoute bestVars = _symbolicDecisions.getBestVars(_optimizations, router, proto);
      assert (bestVars != null);

      BoolExpr acc = null;
      BoolExpr somePermitted = null;

      for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {
        SymbolicRoute vars = correctVars(e);

        if (somePermitted == null) {
          somePermitted = vars.getPermitted();
        } else {
          somePermitted = mkOr(somePermitted, vars.getPermitted());
        }

        BoolExpr v = mkAnd(vars.getPermitted(), equal(conf, proto, bestVars, vars, e, true));
        if (acc == null) {
          acc = v;
        } else {
          acc = mkOr(acc, v);
        }
        add(mkImplies(vars.getPermitted(), greaterOrEqual(conf, proto, bestVars, vars, e)));
      }

      if (acc != null) {
        // -----------------------------------------------------------
        add(mkEq(somePermitted, bestVars.getPermitted()));
        // -----------------------------------------------------------
        add(mkImplies(somePermitted, acc));
      }
    }
  }
}
```

```smt
|0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_permitted| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_permitted| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_permitted| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_permitted| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_permitted|) |0_SLICE-MAIN_r2_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_r3_OVERALL_BEST_None_permitted|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_permitted| |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_permitted| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_permitted| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_permitted| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_permitted|) |0_SLICE-MAIN_r3_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_isp1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_isp2_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_isp2_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_isp2_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-MAIN_customer_BGP_BEST_None_permitted|:
(assert (= |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_customer_BGP_BEST_None_permitted|))  Y
|0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_customer_BGP_BEST_None_permitted|))  Y
|0_SLICE-MAIN_customer_CONNECTED_BEST_None_permitted|:
(assert (= |0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| |0_SLICE-MAIN_customer_CONNECTED_BEST_None_permitted|))  Y
|0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|:
(assert (= |0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| |0_SLICE-MAIN_customer_CONNECTED_BEST_None_permitted|))  Y
|0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|:
(assert (= (or |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted| |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_permitted| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted|) |0_SLICE-MAIN_r1_OVERALL_BEST_None_permitted|))  Y

|0_SLICE-r1_r3_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r1_r3_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r1_r3_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r1_r1_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r1_r1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r1_r1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r2_r2_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r2_r2_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r2_r2_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r2_r1_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| |0_SLICE-r2_r1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted|:
(assert (= |0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| |0_SLICE-r2_r1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r3_r3_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r3_r3_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r3_r3_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r3_r1_OVERALL_BEST_None_permitted|:
(assert (= |0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r3_r1_OVERALL_BEST_None_permitted|))  Y
|0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted|:
(assert (= |0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| |0_SLICE-r3_r1_OVERALL_BEST_None_permitted|))  Y

|0_SLICE-MAIN_customer_OVERALL_BEST_None_permitted|:
(assert (= (or |0_SLICE-MAIN_customer_BGP_BEST_None_permitted| |0_SLICE-MAIN_customer_CONNECTED_BEST_None_permitted|) |0_SLICE-MAIN_customer_OVERALL_BEST_None_permitted|))  X
```

------------------------------------------------------------------------------------------

#### EncoderSlice.java Line 1633

```java
private void addChoicePerProtocolConstraints() {
  for (Entry<String, Configuration> entry : getGraph().getConfigurations().entrySet()) {
    String router = entry.getKey();
    Configuration conf = entry.getValue();
    for (Protocol proto : getProtocols().get(router)) {
      SymbolicRoute bestVars = _symbolicDecisions.getBestVars(_optimizations, router, proto);
      assert (bestVars != null);
      for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {
        SymbolicRoute vars = correctVars(e);
        BoolExpr choice = _symbolicDecisions.getChoiceVariables().get(router, proto, e);
        assert (choice != null);
        BoolExpr isBest = equal(conf, proto, bestVars, vars, e, false);
        // -----------------------------------------------------------
        add(mkEq(choice, mkAnd(vars.getPermitted(), isBest)));
        // -----------------------------------------------------------
      }
    }
  }
}
```

```smt
|0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_choice|:
(assert (= |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_choice| (and |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_permitted| (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_prefixLength|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_localPref|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_metric|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet3/0_bgpInternal|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_choice|:
(assert (= |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_choice| (and |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_permitted| (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_prefixLength|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_localPref|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_metric|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_bgpInternal|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r3_igpMetric|))))  Y
|0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_choice|:
(assert (= |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_choice| (and |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_permitted| (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_prefixLength|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_localPref|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_metric|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_bgpInternal|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r2_BGP_IMPORT_iBGP-r1_igpMetric|))))  Y
|0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_permitted| (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_prefixLength|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_localPref|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_metric|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet1/0_choice|:
(assert (= |0_SLICE-MAIN_r2_BGP_IMPORT_GigabitEthernet1/0_choice| (and |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_permitted| (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_prefixLength|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_localPref|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_metric|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|) (= |0_SLICE-MAIN_r2_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_metric|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r1_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_choice|:
(assert (= |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_choice| (and |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_permitted| (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_prefixLength|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_localPref|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_metric|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_bgpInternal|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r1_igpMetric|))))  Y
|0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet1/0_choice|:
(assert (= |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet1/0_choice| (and |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_permitted| (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_prefixLength|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_localPref|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_metric|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet1/0_bgpInternal|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_choice|:
(assert (= |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_choice| (and |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_permitted| (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_prefixLength|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_localPref|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_metric|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r3_BGP_IMPORT_GigabitEthernet2/0_bgpInternal|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_choice|:
(assert (= |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_choice| (and |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_permitted| (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_prefixLength|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_localPref|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_metric|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_bgpInternal|) (= |0_SLICE-MAIN_r3_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r3_BGP_IMPORT_iBGP-r2_igpMetric|))))  Y
|0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_isp1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_isp1_BGP_IMPORT_GigabitEthernet0/0_metric|))))  Y
|0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_isp2_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_isp2_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_isp2_OVERALL_BEST_None_metric| |0_SLICE-MAIN_isp2_BGP_IMPORT_GigabitEthernet0/0_metric|))))  Y
|0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_customer_BGP_BEST_None_prefixLength| |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_customer_BGP_BEST_None_localPref| |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_customer_BGP_BEST_None_metric| |0_SLICE-MAIN_customer_BGP_IMPORT_GigabitEthernet0/0_metric|))))  Y
|0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_choice|:
(assert (= |0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_choice| (and |0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| (= |0_SLICE-MAIN_customer_CONNECTED_BEST_None_prefixLength| |0_SLICE-MAIN_customer_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|))))  Y
|0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_metric|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r3_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_choice|:
(assert (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_choice| (and |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_permitted| (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_prefixLength|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_localPref|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_metric|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_bgpInternal|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r2_igpMetric|))))  Y
|0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_choice|:
(assert (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_choice| (and |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_permitted| (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_prefixLength|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_localPref|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_metric|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet2/0_bgpInternal|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_choice|:
(assert (= |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_choice| (and |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_permitted| (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_prefixLength|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_localPref|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_metric|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_bgpInternal|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_igpMetric| |0_SLICE-MAIN_r1_BGP_IMPORT_iBGP-r3_igpMetric|))))  Y
|0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet1/0_choice|:
(assert (= |0_SLICE-MAIN_r1_BGP_IMPORT_GigabitEthernet1/0_choice| (and |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_localPref| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_localPref|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_metric| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_metric|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_bgpInternal| |0_SLICE-MAIN_r2_BGP_EXPORT_GigabitEthernet0/0_bgpInternal|) (= |0_SLICE-MAIN_r1_OVERALL_BEST_None_igpMetric| 0))))  Y
|0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-r1_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-r1_r3_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-r1_r3_OVERALL_BEST_None_metric| 0))))  Y
|0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-r1_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-r1_r1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-r1_r1_OVERALL_BEST_None_metric| 0))))  Y
|0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-r2_r2_OVERALL_BEST_None_prefixLength| |0_SLICE-r2_r2_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-r2_r2_OVERALL_BEST_None_metric| 0))))  Y
|0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_choice|:
(assert (= |0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_choice| (and |0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_permitted| (= |0_SLICE-r2_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-r2_r1_CONNECTED_IMPORT_GigabitEthernet1/0_prefixLength|) (= |0_SLICE-r2_r1_OVERALL_BEST_None_metric| 0))))  Y
|0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-r3_r3_OVERALL_BEST_None_prefixLength| |0_SLICE-r3_r3_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-r3_r3_OVERALL_BEST_None_metric| 0))))  Y
|0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_choice|:
(assert (= |0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_choice| (and |0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_permitted| (= |0_SLICE-r3_r1_OVERALL_BEST_None_prefixLength| |0_SLICE-r3_r1_CONNECTED_IMPORT_GigabitEthernet0/0_prefixLength|) (= |0_SLICE-r3_r1_OVERALL_BEST_None_metric| 0))))  Y
```

#### EncoderSlice.java Line 1701 and Line 1710

```java
private void addControlForwardingConstraints() {
  for (Entry<String, Configuration> entry : getGraph().getConfigurations().entrySet()) {
    String router = entry.getKey();
    Configuration conf = entry.getValue();
    boolean someEdge = false;

    SymbolicRoute best = _symbolicDecisions.getBestNeighbor().get(router);
    Map<GraphEdge, BoolExpr> cfExprs = new HashMap<>();

    Set<GraphEdge> constrained = new HashSet<>();

    for (Protocol proto : getProtocols().get(router)) {

      for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {

        someEdge = true;
        constrained.add(e.getEdge());

        SymbolicRoute vars = correctVars(e);
        BoolExpr choice = _symbolicDecisions.getChoiceVariables().get(router, proto, e);
        BoolExpr isBest = mkAnd(choice, equal(conf, proto, best, vars, e, false));

        GraphEdge ge = e.getEdge();

        // Connected routes should only forward if not absorbed by interface
        GraphEdge other = getGraph().getOtherEnd().get(ge);
        BoolExpr connectedWillSend;
        if (other == null || getGraph().isHost(ge.getPeer())) {
          Ip ip = ge.getStart().getConcreteAddress().getIp();
          BitVecExpr val = getCtx().mkBV(ip.asLong(), 32);
          connectedWillSend = mkNot(mkEq(_symbolicPacket.getDstIp(), val));
        } else {
          Ip ip = other.getStart().getConcreteAddress().getIp();
          BitVecExpr val = getCtx().mkBV(ip.asLong(), 32);
          connectedWillSend = mkEq(_symbolicPacket.getDstIp(), val);
        }
        BoolExpr canSend = (proto.isConnected() ? connectedWillSend : mkTrue());

        BoolExpr sends = mkAnd(canSend, isBest);

        BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
        assert (cForward != null);
        add(mkImplies(sends, cForward));

        // record the negation as well
        cfExprs.merge(ge, sends, (a, b) -> mkOr(a, b));
      }
    }

    // For edges that are never used, we constraint them to not be forwarded out of
    for (GraphEdge ge : getGraph().getEdgeMap().get(router)) {
      if (!constrained.contains(ge)) {
        BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
        assert (cForward != null);
        // -----------------------------------------------------------
        add(mkNot(cForward));
        // -----------------------------------------------------------
      }
    }

    // Handle the case that the router has no protocol running
    if (!someEdge) {
      for (GraphEdge ge : getGraph().getEdgeMap().get(router)) {
        BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
        assert (cForward != null);
        // -----------------------------------------------------------
        add(mkNot(cForward));
        // -----------------------------------------------------------
      }
    } else {
      // If no best route, then no forwarding
      Map<Protocol, List<ArrayList<LogicalEdge>>> map =
          _logicalGraph.getLogicalEdges().get(router);

      Set<GraphEdge> seen = new HashSet<>();
      for (List<ArrayList<LogicalEdge>> eList : map.values()) {
        for (ArrayList<LogicalEdge> edges : eList) {
          for (LogicalEdge le : edges) {
            GraphEdge ge = le.getEdge();
            if (seen.contains(ge)) {
              continue;
            }
            seen.add(ge);
            BoolExpr expr = cfExprs.get(ge);
            BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
            assert (cForward != null);
            if (expr != null) {
              add(mkImplies(mkNot(expr), mkNot(cForward)));
            } else {
              add(mkNot(cForward));
            }
          }
        }
      }
    }
  }
}
```

```smt
|0_SLICE-MAIN_CONTROL-FORWARDING_r2_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_r3_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp1_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet1/0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp2_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_customer_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_customer_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_r1_Loopback0|:
(assert (not |0_SLICE-MAIN_CONTROL-FORWARDING_r1_Loopback0|))  Y

|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r3|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r3|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r3|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r1|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r1|))  Y
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r2_iBGP-r1|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_Loopback0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_iBGP-r2|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r3_iBGP-r2|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_iBGP-r1|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r3_iBGP-r1|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_Loopback0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet1/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_iBGP-r2|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r1_iBGP-r2|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_iBGP-r3|:
(assert (not |0_SLICE-r1_CONTROL-FORWARDING_r1_iBGP-r3|))  Y

|0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_Loopback0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_iBGP-r3|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r2_iBGP-r3|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_iBGP-r1|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r2_iBGP-r1|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r2|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r2|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r2|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r1|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r1|))  Y
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r3_iBGP-r1|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_Loopback0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet0/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_iBGP-r2|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r1_iBGP-r2|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_iBGP-r3|:
(assert (not |0_SLICE-r2_CONTROL-FORWARDING_r1_iBGP-r3|))  Y

|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r3|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r3|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r3|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r1|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r1|))  Y
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r2_iBGP-r1|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_Loopback0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_iBGP-r2|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r3_iBGP-r2|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_iBGP-r1|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r3_iBGP-r1|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_Loopback0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_iBGP-r2|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_iBGP-r2|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_iBGP-r3|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_iBGP-r3|))  Y

|0_SLICE-r1_r2_OVERALL_BEST_None_permitted|:
(assert (not |0_SLICE-r1_r2_OVERALL_BEST_None_permitted|))  X

|0_SLICE-r2_r3_OVERALL_BEST_None_permitted|:
(assert (not |0_SLICE-r2_r3_OVERALL_BEST_None_permitted|))  X

|0_SLICE-r3_r2_OVERALL_BEST_None_permitted|:
(assert (not |0_SLICE-r3_r2_OVERALL_BEST_None_permitted|))  X
```

#### EncoderSlice.java Line 1827

```java
private void addDataForwardingConstraints() {
  for (Entry<String, List<GraphEdge>> entry : getGraph().getEdgeMap().entrySet()) {
    String router = entry.getKey();
    List<GraphEdge> edges = entry.getValue();

    for (GraphEdge ge : edges) {
      // setup forwarding for non-abstract edges
      if (!ge.isAbstract()) {
        BoolExpr fwd = mkFalse();
        BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
        BoolExpr dForward = _symbolicDecisions.getDataForwarding().get(router, ge);
        assert (cForward != null);
        assert (dForward != null);

        // for each abstract control edge,
        // if that edge is on and its neighbor slices has next hop forwarding
        // out the current edge ge, the we use ge.
        for (GraphEdge ge2 : getGraph().getEdgeMap().get(router)) {
          if (ge2.isAbstract()) {
            BoolExpr ctrlFwd = getSymbolicDecisions().getControlForwarding().get(router, ge2);
            Graph.BgpSendType st = getGraph().peerType(ge2);
            // If Route reflectors, then next hop based on ID
            if (st == Graph.BgpSendType.TO_RR) {
              SymbolicRoute record = getSymbolicDecisions().getBestNeighbor().get(router);
              // adjust for iBGP in main slice
              BoolExpr acc = mkFalse();
              if (isMainSlice()) {
                for (Entry<String, Integer> entry2 : getGraph().getOriginatorId().entrySet()) {
                  String r = entry2.getKey();
                  Integer id = entry2.getValue();
                  EncoderSlice s = _encoder.getSlice(r);
                  // Make sure
                  if (otherSliceHasEdge(s, router, ge)) {
                    BoolExpr outEdge =
                        s.getSymbolicDecisions().getDataForwarding().get(router, ge);
                    acc = mkOr(acc, mkAnd(record.getClientId().checkIfValue(id), outEdge));
                  }
                }
              }
              fwd = mkOr(fwd, mkAnd(ctrlFwd, acc));

            } else {
              // Otherwise, we know the next hop statically
              // adjust for iBGP in main slice
              if (isMainSlice()) {
                EncoderSlice s = _encoder.getSlice(ge2.getPeer());
                if (otherSliceHasEdge(s, router, ge)) {
                  BoolExpr outEdge = s.getSymbolicDecisions().getDataForwarding().get(router, ge);
                  fwd = mkOr(fwd, mkAnd(ctrlFwd, outEdge));
                }
              }
            }
          }
        }

        fwd = mkOr(fwd, cForward);
        BoolExpr acl = _outboundAcls.get(ge);
        if (acl == null) {
          acl = mkTrue();
        }
        BoolExpr notBlocked = mkAnd(fwd, acl);
        // -----------------------------------------------------------
        add(mkEq(notBlocked, dForward));
        // -----------------------------------------------------------
      }
    }
  }
}
```

```smt
|0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r2_GigabitEthernet0/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet0/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r2_GigabitEthernet1/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet1/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r2_Loopback0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r2_Loopback0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r2_Loopback0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r2_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r2_Loopback0|)) |0_SLICE-MAIN_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-MAIN_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y

|0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r3_GigabitEthernet0/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet0/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet0/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r3_Loopback0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r3_Loopback0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r3_Loopback0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r3_Loopback0|)) |0_SLICE-MAIN_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r3_GigabitEthernet1/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet1/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r3_iBGP-r1| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet1/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y

|0_SLICE-MAIN_DATA-FORWARDING_isp1_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp1_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp1_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_isp1_GigabitEthernet1/0|))  Y

|0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_isp2_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp2_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_isp2_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_isp2_GigabitEthernet0/0|))  Y

|0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet1/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet1/0| |0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet1/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_customer_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_customer_Loopback0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_customer_Loopback0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_Loopback0| |0_SLICE-MAIN_DATA-FORWARDING_customer_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet0/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_customer_GigabitEthernet0/0| |0_SLICE-MAIN_DATA-FORWARDING_customer_GigabitEthernet0/0|))  Y

|0_SLICE-MAIN_DATA-FORWARDING_r1_Loopback0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r1_Loopback0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r1_Loopback0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r1_Loopback0|)) |0_SLICE-MAIN_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet0/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet0/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet0/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= (or |0_SLICE-MAIN_CONTROL-FORWARDING_r1_GigabitEthernet1/0| (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r2| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet1/0|) (and |0_SLICE-MAIN_CONTROL-FORWARDING_r1_iBGP-r3| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet1/0|)) |0_SLICE-MAIN_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y

|0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r1_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r1_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r1_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r1_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r1_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y

|0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r2_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r2_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r2_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r2_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r2_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y

|0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet0/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet1/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r2_Loopback0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r2_GigabitEthernet3/0| |0_SLICE-r3_DATA-FORWARDING_r2_GigabitEthernet3/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet0/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r3_Loopback0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet1/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet1/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet2/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r3_GigabitEthernet2/0| |0_SLICE-r3_DATA-FORWARDING_r3_GigabitEthernet2/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_Loopback0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_Loopback0| |0_SLICE-r3_DATA-FORWARDING_r1_Loopback0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet0/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet0/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet0/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet1/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0|:
(assert (not |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0|))
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet1/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet1/0|))  Y
|0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
|0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet2/0|:
(assert (= |0_SLICE-r3_CONTROL-FORWARDING_r1_GigabitEthernet2/0| |0_SLICE-r3_DATA-FORWARDING_r1_GigabitEthernet2/0|))  Y
```

==========================================================================================

#### PropertyChecker.java Line 531

```java
private AnswerElement checkProperty(
    NetworkSnapshot snapshot,
    HeaderLocationQuestion qOrig,
    TriFunction<Encoder, Set<String>, Set<GraphEdge>, Map<String, BoolExpr>> instrument,
    Function<VerifyParam, AnswerElement> answer) {

  long totalTime = System.currentTimeMillis();
  // Note: Configure Graph _bddBasedAnalysis to false by default.
  //   * true:  BDD-based analysis
  //   * false: SMT-based analysis
  Graph graph = new Graph(_batfish, snapshot);
  PathRegexes p = new PathRegexes(qOrig);

  // Filter GrapeEdge.
  //   * match _dstRegex and not match _notDstRegex
  //     + if not GrapeEdge.isAbstract()
  //       - match _ifaceRegex and not match _notIfaceRegex
  Set<GraphEdge> destPorts = findFinalInterfaces(graph, p);
  // Filter Router(String).
  //   * match _srcRegex and not match _notSrcRegex
  List<String> sourceRouters = PatternUtils.findMatchingSourceNodes(graph, p);

  if (destPorts.isEmpty()) {
    throw new BatfishException("Set of valid destination interfaces is empty");
  }
  if (sourceRouters.isEmpty()) {
    throw new BatfishException("Set of valid ingress nodes is empty");
  }

  // copy before updating header space, so these changes don't get propagated to the answer
  HeaderLocationQuestion q = new HeaderLocationQuestion(qOrig);
  q.setHeaderSpace(q.getHeaderSpace().toBuilder().build());
  // Infer dstIps and notDstIps in HeaderLocationQuestion HeaderSpace.
  // * isExternal interface
  //   + it can be any prefix, leave it unconstrained
  //   + set headerSpace.setDstIps    (Collections.emptySet())
  //   + set headerSpace.setNotDstIps (Collections.emptySet())
  // * isNull (ge.getPeer() == null)
  //   + set headerSpace.setDstIps    (ge.getStart() IpSpaces)
  // * isHost
  //   + set headerSpace.setDstIps    (ge.getStart() IpSpaces)
  //   + set headerSpace.setNotDstIps (ge.getEnd()   exact Ip address)
  // * otherwise
  //   + set headerSpace.setDstIps    (ge.getStart() exact Ip address)
  inferDestinationHeaderSpace(graph, destPorts, q);

  // Identify all GraphEdges that are allowed to fail optionally.
  Set<GraphEdge> failOptions = failLinkSet(graph, q);
  // Identify all Routers that are allowed to fail optionally.
  Set<String> failNodeOptions = failNodeSet(graph, q);

  // When HeaderQuestion abstraction is enabled, enable network slices.
  Tuple<Stream<Supplier<NetworkSlice>>, Long> ecs = findAllNetworkSlices(q, graph, true);
  Stream<Supplier<NetworkSlice>> stream = ecs.getFirst();
  Long timeAbstraction = ecs.getSecond();

  AnswerElement[] answerElement = new AnswerElement[1];
  VerificationResult[] result = new VerificationResult[2];
  List<VerificationStats> ecStats = new ArrayList<>();

  // Checks ECs in parallel, but short circuits when a counterexample is found
  boolean hasCounterExample =
      stream.anyMatch(
          lazyEc -> {
            long timeEc = System.currentTimeMillis();
            NetworkSlice slice = lazyEc.get();
            timeEc = System.currentTimeMillis() - timeEc;

            synchronized (_lock) {
              // Make sure the headerspace is correct
              HeaderLocationQuestion question = new HeaderLocationQuestion(q);
              question.setHeaderSpace(slice.getHeaderSpace());

              // Get the EC graph and mapping
              Graph g = slice.getGraph();
              // TODO concrete nodes -> abstract nodes
              Set<String> srcRouters = mapConcreteToAbstract(slice, sourceRouters);

              long timeEncoding = System.currentTimeMillis();
              // TODO: initialize Encoder ...
              // TODO: initialize EncoderSlice ...
              Encoder enc = new Encoder(g, question);
              // TODO: call Encoder computeEncoding ..., add some basic constraints ?
              // TODO: call EncoderSlice computeEncoding ...
              enc.computeEncoding();
              timeEncoding = System.currentTimeMillis() - timeEncoding;

              // Add environment constraints for base case
              if (question.getDiffType() != null) {
                if (question.getEnvDiff()) {
                  addEnvironmentConstraints(enc, question.getDeltaEnvironmentType());
                }
              } else {
                addEnvironmentConstraints(enc, question.getBaseEnvironmentType());
              }

              // This function dispatches to the PropertyAdder.instrumentxxx method.
              // Call PropertyAdder instrumentReachability for checkReachability.
              //   (initialReachability and resursiveReachability)
              // Call PropertyAdder instrumentLoad for checkLoadBalancing.
              Map<String, BoolExpr> prop = instrument.apply(enc, srcRouters, destPorts);

              // If this is a equivalence query, we create a second copy of the network
              Encoder enc2 = null;
              Map<String, BoolExpr> prop2 = null;

              if (question.getDiffType() != null) {
                HeaderLocationQuestion q2 = new HeaderLocationQuestion(question);
                // Set the number of link failure (GraphEdges) to 0, no failed GrphEdge.
                q2.setFailures(0);
                long timeDiffEncoding = System.currentTimeMillis();
                enc2 = new Encoder(enc, g, q2);
                enc2.computeEncoding();
                timeDiffEncoding = System.currentTimeMillis() - timeDiffEncoding;
                timeEncoding += timeDiffEncoding;
              }

              if (question.getDiffType() != null) {
                assert (enc2 != null);
                // create a map for enc2 to lookup a related environment variable from enc
                Table2<GraphEdge, EdgeType, SymbolicRoute> relatedEnv = new Table2<>();
                enc2.getMainSlice()
                    .getLogicalGraph()
                    .getEnvironmentVars()
                    .forEach((lge, r) -> relatedEnv.put(lge.getEdge(), lge.getEdgeType(), r));

                BoolExpr related = enc.mkTrue();
                addEnvironmentConstraints(enc2, question.getBaseEnvironmentType());

                if (!question.getEnvDiff()) {
                  related = relateEnvironments(enc, enc2);
                }

                prop2 = instrument.apply(enc2, srcRouters, destPorts);

                // Add diff constraints
                BoolExpr required = enc.mkTrue();
                for (String source : srcRouters) {
                  BoolExpr sourceProp1 = prop.get(source);
                  BoolExpr sourceProp2 = prop2.get(source);
                  BoolExpr val;
                  switch (q.getDiffType()) {
                    case INCREASED:
                      val = enc.mkImplies(sourceProp1, sourceProp2);
                      break;
                    case REDUCED:
                      val = enc.mkImplies(sourceProp2, sourceProp1);
                      break;
                    case ANY:
                      val = enc.mkEq(sourceProp1, sourceProp2);
                      break;
                    default:
                      throw new BatfishException("Missing case: " + q.getDiffType());
                  }
                  required = enc.mkAnd(required, val);
                }

                related = enc.mkAnd(related, relatePackets(enc, enc2));
                enc.add(related);
                enc.add(enc.mkNot(required));

              } else {
                // Not a differential query; just a query on a single version of the network.
                BoolExpr allProp = enc.mkTrue();
                for (String router : srcRouters) {
                  BoolExpr r = prop.get(router);
                  // NOTE: Choose original network property or negated network property.
                  // Enable negate flag to verify isolation property via checkReachability method.
                  if (q.getNegate()) {
                    r = enc.mkNot(r);
                  }
                  allProp = enc.mkAnd(allProp, r);
                }
                // Negate this network property for verification.
                // ---------------------------------------------------
                enc.add(enc.mkNot(allProp));
                // ---------------------------------------------------
              }

              addLinkFailureConstraints(enc, destPorts, failOptions);
              addNodeFailureConstraints(enc, failNodeOptions);

              // Call Solver.check to verify and print relevant information.
              Tuple<VerificationResult, Model> tup = enc.verify();
              VerificationResult res = tup.getFirst();
              Model model = tup.getSecond();

              if (q.getBenchmark()) {
                VerificationStats stats = res.getStats();
                stats.setAvgComputeEcTime(timeEc);
                stats.setMaxComputeEcTime(timeEc);
                stats.setMinComputeEcTime(timeEc);
                stats.setAvgEncodingTime(timeEncoding);
                stats.setMaxEncodingTime(timeEncoding);
                stats.setMinEncodingTime(timeEncoding);
                stats.setTimeCreateBdds((double) timeAbstraction);

                synchronized (_lock) {
                  ecStats.add(stats);
                }
              }

              if (!res.isVerified()) {
                VerifyParam vp = new VerifyParam(res, model, srcRouters, enc, enc2, prop, prop2);
                AnswerElement ae = answer.apply(vp);
                synchronized (_lock) {
                  answerElement[0] = ae;
                  result[0] = res;
                }
                return true;
              }

              synchronized (_lock) {
                result[1] = res;
              }
              return false;
            }
          });

  totalTime = (System.currentTimeMillis() - totalTime);
  VerificationResult res;
  AnswerElement ae;
  if (hasCounterExample) {
    res = result[0];
    ae = answerElement[0];
  } else {
    res = result[1];
    VerifyParam vp = new VerifyParam(res, null, null, null, null, null, null);
    ae = answer.apply(vp);
  }
  if (q.getBenchmark()) {
    VerificationStats stats = VerificationStats.combineAll(ecStats, totalTime);
    res.setStats(stats);
  }
  return ae;
}
```

```smt
|0_SLICE-MAIN__reachable_isp2|:
(assert (not |0_SLICE-MAIN__reachable_isp2|))  Y
```

==========================================================================================

|0_SLICE-r1_dst-ip|:
(assert (and (= |0_SLICE-r1_dst-ip| #xc0120101) (= |0_SLICE-r1_dst-port| 179) (= |0_SLICE-r1_ip-protocol| 6)))
|0_SLICE-r1_dst-port|:
(assert (and (= |0_SLICE-r1_dst-ip| #xc0120101) (= |0_SLICE-r1_dst-port| 179) (= |0_SLICE-r1_ip-protocol| 6)))
|0_SLICE-r1_ip-protocol|:
(assert (and (= |0_SLICE-r1_dst-ip| #xc0120101) (= |0_SLICE-r1_dst-port| 179) (= |0_SLICE-r1_ip-protocol| 6)))

|0_SLICE-r2_dst-ip|:
(assert (and (= |0_SLICE-r2_dst-ip| #xc0120106) (= |0_SLICE-r2_dst-port| 179) (= |0_SLICE-r2_ip-protocol| 6)))
|0_SLICE-r2_dst-port|:
(assert (and (= |0_SLICE-r2_dst-ip| #xc0120106) (= |0_SLICE-r2_dst-port| 179) (= |0_SLICE-r2_ip-protocol| 6)))
|0_SLICE-r2_ip-protocol|:
(assert (and (= |0_SLICE-r2_dst-ip| #xc0120106) (= |0_SLICE-r2_dst-port| 179) (= |0_SLICE-r2_ip-protocol| 6)))

|0_SLICE-r3_dst-ip|:
(assert (and (= |0_SLICE-r3_dst-ip| #xc0120102) (= |0_SLICE-r3_dst-port| 179) (= |0_SLICE-r3_ip-protocol| 6)))
|0_SLICE-r3_dst-port|:
(assert (and (= |0_SLICE-r3_dst-ip| #xc0120102) (= |0_SLICE-r3_dst-port| 179) (= |0_SLICE-r3_ip-protocol| 6)))
|0_SLICE-r3_ip-protocol|:
(assert (and (= |0_SLICE-r3_dst-ip| #xc0120102) (= |0_SLICE-r3_dst-port| 179) (= |0_SLICE-r3_ip-protocol| 6)))
