package org.batfish.minesweeper.smt;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Tactic;

import java.io.*;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.annotation.Nullable;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpPeerConfig;
import org.batfish.datamodel.HeaderSpace;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.IpProtocol;
import org.batfish.datamodel.IpWildcard;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.SubRange;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.Graph;
import org.batfish.minesweeper.GraphEdge;
import org.batfish.minesweeper.OspfType;
import org.batfish.minesweeper.Protocol;
import org.batfish.minesweeper.question.HeaderQuestion;
import org.batfish.minesweeper.utils.MsPair;
import org.batfish.minesweeper.utils.Tuple;

import java.util.ArrayList;
import java.util.stream.Collectors;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.AsPathListExpr;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.BooleanExprs;
import org.batfish.datamodel.routing_policy.expr.CallExpr;
import org.batfish.datamodel.routing_policy.expr.CommunitySetExpr;
import org.batfish.datamodel.routing_policy.expr.Conjunction;
import org.batfish.datamodel.routing_policy.expr.ConjunctionChain;
import org.batfish.datamodel.routing_policy.expr.DecrementLocalPreference;
import org.batfish.datamodel.routing_policy.expr.DecrementMetric;
import org.batfish.datamodel.routing_policy.expr.Disjunction;
import org.batfish.datamodel.routing_policy.expr.ExplicitPrefixSet;
import org.batfish.datamodel.routing_policy.expr.FirstMatchChain;
import org.batfish.datamodel.routing_policy.expr.IncrementLocalPreference;
import org.batfish.datamodel.routing_policy.expr.IncrementMetric;
import org.batfish.datamodel.routing_policy.expr.IntExpr;
import org.batfish.datamodel.routing_policy.expr.LiteralAsList;
import org.batfish.datamodel.routing_policy.expr.LiteralInt;
import org.batfish.datamodel.routing_policy.expr.LiteralLong;
import org.batfish.datamodel.routing_policy.expr.LongExpr;
import org.batfish.datamodel.routing_policy.expr.MatchAsPath;
import org.batfish.datamodel.routing_policy.expr.MatchCommunitySet;
import org.batfish.datamodel.routing_policy.expr.MatchIpv4;
import org.batfish.datamodel.routing_policy.expr.MatchIpv6;
import org.batfish.datamodel.routing_policy.expr.MatchPrefix6Set;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.expr.MatchProtocol;
import org.batfish.datamodel.routing_policy.expr.MultipliedAs;
import org.batfish.datamodel.routing_policy.expr.NamedCommunitySet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
import org.batfish.datamodel.routing_policy.expr.Not;
import org.batfish.datamodel.routing_policy.expr.PrefixSetExpr;
import org.batfish.datamodel.routing_policy.expr.WithEnvironmentExpr;
import org.batfish.datamodel.routing_policy.statement.AddCommunity;
import org.batfish.datamodel.routing_policy.statement.DeleteCommunity;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.PrependAsPath;
import org.batfish.datamodel.routing_policy.statement.SetCommunity;
import org.batfish.datamodel.routing_policy.statement.SetDefaultPolicy;
import org.batfish.datamodel.routing_policy.statement.SetLocalPreference;
import org.batfish.datamodel.routing_policy.statement.SetMetric;
import org.batfish.datamodel.routing_policy.statement.SetNextHop;
import org.batfish.datamodel.routing_policy.statement.SetOrigin;
import org.batfish.datamodel.routing_policy.statement.SetOspfMetricType;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements.StaticStatement;

import org.batfish.datamodel.PrefixRange;

/**
 * A class responsible for building a symbolic encoding of the entire network. The encoder does this
 * by maintaining a collection of encoding slices, where each slice encodes the forwarding behavior
 * for a particular packet.
 *
 * <p>The encoder object is architected this way to allow for modeling of features such as iBGP or
 * non-local next-hop ip addresses in static routes, where the forwarding behavior of one packet
 * depends on that of other packets.
 *
 * <p>Symbolic variables that are common to all slices are maintained in this class. That includes,
 * for example, the collection of variables representing topology failures.
 *
 * @author Ryan Beckett
 */
public class Encoder {
  // enable debugging
  static final Boolean ENABLE_DEBUGGING = false;
  static final String MAIN_SLICE_NAME = "SLICE-MAIN_";
  private static final boolean ENABLE_UNSAT_CORE = false;
  // Encoder object identifier, the default configuration is 0
  private int _encodingId;
  // the default configuration is true
  private boolean _modelIgp;

  private HeaderQuestion _question;
  // NOTE: <HostName, EncoderSlice>
  private Map<String, EncoderSlice> _slices;
  // NOTE: <HostName, Map<OtherHostName, BoolExpr>>
  // TODO: annotated by yongzheng on 20250318
  private Map<String, Map<String, BoolExpr>> _sliceReachability;

  private Encoder _previousEncoder;
  // a collection of symbolic variables representing the possible link failures
  private SymbolicFailures _symbolicFailures;
  // a map of all smt variables, the relevant format is <Expr.toString(), Expr>
  private Map<String, Expr> _allVariables;

  private Graph _graph;

  private Context _ctx;

  private Solver _solver;

  private UnsatCore _unsatCore;

  // the output directory name and relevant print writer
  private String _outputDirectoryName;
  PrintWriter _smtWriter;
  PrintWriter _constWriter;
  PrintWriter _configWriter;

  /**
   * Create an encoder object that will consider all packets in the provided headerspace.
   *
   * @param graph The network graph
   */
  Encoder(Graph graph, HeaderQuestion q) {
    this(null, graph, q, null, null, null, 0);
  }

  /**
   * Create an encoder object from an existing encoder.
   *
   * @param e An existing encoder object
   * @param g An existing network graph
   */
  Encoder(Encoder e, Graph g) {
    this(e, g, e._question, e.getCtx(), e.getSolver(), e.getAllVariables(), e.getId() + 1);
  }

  /**
   * Create an encoder object from an existing encoder.
   *
   * @param e An existing encoder object
   * @param g An existing network graph
   * @param q A header question
   */
  Encoder(Encoder e, Graph g, HeaderQuestion q) {
    this(e, g, q, e.getCtx(), e.getSolver(), e.getAllVariables(), e.getId() + 1);
  }

  /**
   * Create an encoder object while possibly reusing the partial encoding of another encoder. If the
   * context and solver are null, then a new encoder is created. Otherwise the old encoder is used.
   */
  private Encoder(
      @Nullable Encoder enc,
      Graph graph,
      HeaderQuestion q,
      @Nullable Context ctx,
      @Nullable Solver solver,
      @Nullable Map<String, Expr> vars,
      int id) {
    _graph = graph;
    _previousEncoder = enc;
    _modelIgp = true;
    _encodingId = id;
    _question = q;
    _slices = new HashMap<>();
    _sliceReachability = new HashMap<>();

    HashMap<String, String> cfg = new HashMap<>();

    // allows for unsat core when debugging
    if (ENABLE_UNSAT_CORE) {
      cfg.put("proof", "true");
      cfg.put("auto-config", "false");
    }

    _ctx = (ctx == null ? new Context(cfg) : ctx);

    if (solver == null) {
      if (ENABLE_UNSAT_CORE) {
        _solver = _ctx.mkSolver();
      } else {
        // The following string, such as "simplify", "propagate-values", "solve-eqs", ...
        // are hardcoded in Z3 and have a fixed meaning and fixed functionality.
        // The following code line that make a specific tactic pipeline.
        Tactic t1 = _ctx.mkTactic("simplify");
        Tactic t2 = _ctx.mkTactic("propagate-values");
        Tactic t3 = _ctx.mkTactic("solve-eqs");
        Tactic t4 = _ctx.mkTactic("bit-blast");
        Tactic t5 = _ctx.mkTactic("smt");
        Tactic t = _ctx.then(t1, t2, t3, t4, t5);
        _solver = _ctx.mkSolver(t);
        // System.out.println("Help: \n" + _solver.getHelp());
      }
    } else {
      _solver = solver;
    }

    _symbolicFailures = new SymbolicFailures(_ctx);

    if (vars == null) {
      _allVariables = new HashMap<>();
    } else {
      _allVariables = vars;
    }

    if (ENABLE_DEBUGGING) {
      System.out.println(graph);
    }

    _unsatCore = new UnsatCore(ENABLE_UNSAT_CORE);

    // initialize output directory and relevant file print writer
    initOutput();

    // initialize configuration constant - SMT symbolic variable
    // initConfigurationConstants();

    // initialize _symbolicFailures and _allVariables, which involving
    //   + all GraphEdge getPeer() == null according to _edgeMap  (_failedEdgeLinks)
    //   + all neighbor node pair according to _neighbors         (_failedInternalLinks)
    initFailedLinkVariables();
    // initialize _symbolicFailures and _allVariables, which involving
    //   + all node according to _routers                         (_failedNodes)
    initFailedNodeVariables();

    // initialize _slices
    //   + one main slice (or only one null slice)
    //   + other slices according to domain (i.e. ibgp neighbors)
    // initialize _sliceReachability (call PropertyAdder instrumentReachability)
    initSlices(_question.getHeaderSpace(), graph);
  }

  /*
   * Initialize symbolic variables to represent link failures.
   */
  private void initFailedLinkVariables() {
    // initialize all isNullPeer GraphEdge, i.e. GraphEdge.getPeer() == null
    for (List<GraphEdge> edges : _graph.getEdgeMap().values()) {
      for (GraphEdge ge : edges) {
        if (ge.getPeer() == null) {
          Interface i = ge.getStart();
          String name = getId() + "_FAILED-EDGE_" + ge.getRouter() + "_" + i.getName();
          ArithExpr var = getCtx().mkIntConst(name);
          _symbolicFailures.getFailedEdgeLinks().put(ge, var);
          _allVariables.put(var.toString(), var);
        }
      }
    }

    // initialize all neighbor node pair, recorded in Graph Map<String, Set<String>> _neighbors
    for (Entry<String, Set<String>> entry : _graph.getNeighbors().entrySet()) {
      String router = entry.getKey();
      Set<String> peers = entry.getValue();
      for (String peer : peers) {
        // sort names for unique
        String pair = (router.compareTo(peer) < 0 ? router + "_" + peer : peer + "_" + router);
        String name = getId() + "_FAILED-EDGE_" + pair;
        ArithExpr var = _ctx.mkIntConst(name);
        _symbolicFailures.getFailedInternalLinks().put(router, peer, var);
        _allVariables.put(var.toString(), var);
      }
    }
  }

  /*
   * Initialize symbolic variables to represent node failures.
   */
  private void initFailedNodeVariables() {
    // initialize all node, recorded in Graph Set<String> _routers
    for (String router : _graph.getRouters()) {
      String name = getId() + "_FAILED-NODE_" + router;
      ArithExpr var = _ctx.mkIntConst(name);
      _symbolicFailures.getFailedNodes().put(router, var);
      _allVariables.put(var.toString(), var);
    }
  }

  /*
   * Initialize each encoding slice.
   * For iBGP, we also add reachability information for each pair of neighbors,
   * to determine if messages sent to/from a neighbor will arrive.
   */
  private void initSlices(HeaderSpace h, Graph g) {
    if (g.getIbgpNeighbors().isEmpty() || !_modelIgp) {
      _slices.put(MAIN_SLICE_NAME, new EncoderSlice(this, h, g, ""));
    } else {
      _slices.put(MAIN_SLICE_NAME, new EncoderSlice(this, h, g, MAIN_SLICE_NAME));
    }

    if (_modelIgp) {
      SortedSet<MsPair<String, Ip>> ibgpRouters = new TreeSet<>();

      for (Entry<GraphEdge, BgpActivePeerConfig> entry : g.getIbgpNeighbors().entrySet()) {
        GraphEdge ge = entry.getKey();
        BgpPeerConfig n = entry.getValue();

        String router = ge.getRouter();
        Ip ip = n.getLocalIp();
        MsPair<String, Ip> pair = new MsPair<>(router, ip);

        // Add one slice per (router, source ip) pair
        if (!ibgpRouters.contains(pair)) {

          ibgpRouters.add(pair);

          // Create a control plane slice only for this ip
          HeaderSpace hs = new HeaderSpace();

          // Make sure messages are sent to this destination IP
          SortedSet<IpWildcard> ips = new TreeSet<>();
          ips.add(IpWildcard.create(n.getLocalIp()));
          hs.setDstIps(ips);

          // Make sure messages use TCP port 179
          SortedSet<SubRange> dstPorts = new TreeSet<>();
          dstPorts.add(SubRange.singleton(179));
          hs.setDstPorts(dstPorts);

          // Make sure messages use the TCP protocol
          SortedSet<IpProtocol> protocols = new TreeSet<>();
          protocols.add(IpProtocol.TCP);
          hs.setIpProtocols(protocols);

          // TODO: create domains once
          Graph gNew = new Graph(g.getBatfish(), g.getSnapshot(), null, g.getDomain(router));
          String sliceName = "SLICE-" + router + "_";
          EncoderSlice slice = new EncoderSlice(this, hs, gNew, sliceName);
          _slices.put(sliceName, slice);

          // TODO: annotated by yongzheng on 20250319
          PropertyAdder pa = new PropertyAdder(slice);
          Map<String, BoolExpr> reachVars = pa.instrumentReachability(router);
          _sliceReachability.put(router, reachVars);
        }
      }
    }
  }

  // Create a symbolic boolean
  BoolExpr mkBool(boolean val) {
    return getCtx().mkBool(val);
  }

  // Symbolic boolean negation
  BoolExpr mkNot(BoolExpr e) {
    return getCtx().mkNot(e);
  }

  // Symbolic boolean disjunction
  BoolExpr mkOr(BoolExpr... vals) {
    return getCtx().mkOr(Arrays.stream(vals).filter(Objects::nonNull).toArray(BoolExpr[]::new));
  }

  // Symbolic boolean implication
  BoolExpr mkImplies(BoolExpr e1, BoolExpr e2) {
    return getCtx().mkImplies(e1, e2);
  }

  // Symbolic boolean conjunction
  BoolExpr mkAnd(BoolExpr... vals) {
    return getCtx().mkAnd(Arrays.stream(vals).filter(Objects::nonNull).toArray(BoolExpr[]::new));
  }

  // Symbolic true value
  BoolExpr mkTrue() {
    return getCtx().mkBool(true);
  }

  // Symbolic false value
  BoolExpr mkFalse() {
    return getCtx().mkBool(false);
  }

  // Symbolic arithmetic less than
  BoolExpr mkLt(Expr e1, Expr e2) {
    if (e1 instanceof BoolExpr && e2 instanceof BoolExpr) {
      return mkAnd((BoolExpr) e2, mkNot((BoolExpr) e1));
    }
    if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
      return getCtx().mkLt((ArithExpr) e1, (ArithExpr) e2);
    }
    if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
      return getCtx().mkBVULT((BitVecExpr) e1, (BitVecExpr) e2);
    }
    throw new BatfishException("Invalid call to mkLt while encoding control plane");
  }

  // Symbolic greater than
  BoolExpr mkGt(Expr e1, Expr e2) {
    if (e1 instanceof BoolExpr && e2 instanceof BoolExpr) {
      return mkAnd((BoolExpr) e1, mkNot((BoolExpr) e2));
    }
    if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
      return getCtx().mkGt((ArithExpr) e1, (ArithExpr) e2);
    }
    if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
      return getCtx().mkBVUGT((BitVecExpr) e1, (BitVecExpr) e2);
    }
    throw new BatfishException("Invalid call the mkLe while encoding control plane");
  }

  // Symbolic arithmetic subtraction
  ArithExpr mkSub(ArithExpr e1, ArithExpr e2) {
    return getCtx().mkSub(e1, e2);
  }

  // Symbolic if-then-else for booleans
  BoolExpr mkIf(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
    return (BoolExpr) getCtx().mkITE(cond, case1, case2);
  }

  // Symbolic if-then-else for arithmetic
  ArithExpr mkIf(BoolExpr cond, ArithExpr case1, ArithExpr case2) {
    return (ArithExpr) getCtx().mkITE(cond, case1, case2);
  }

  // Create a symbolic integer
  ArithExpr mkInt(long l) {
    return getCtx().mkInt(l);
  }

  // Symbolic arithmetic addition
  ArithExpr mkSum(ArithExpr e1, ArithExpr e2) {
    return getCtx().mkAdd(e1, e2);
  }

  // Symbolic greater than or equal to
  BoolExpr mkGe(Expr e1, Expr e2) {
    if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
      return getCtx().mkGe((ArithExpr) e1, (ArithExpr) e2);
    }
    if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
      return getCtx().mkBVUGE((BitVecExpr) e1, (BitVecExpr) e2);
    }
    throw new BatfishException("Invalid call to mkGe while encoding control plane");
  }

  // Symbolic less than or equal to
  BoolExpr mkLe(Expr e1, Expr e2) {
    if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
      return getCtx().mkLe((ArithExpr) e1, (ArithExpr) e2);
    }
    if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
      return getCtx().mkBVULE((BitVecExpr) e1, (BitVecExpr) e2);
    }
    throw new BatfishException("Invalid call to mkLe while encoding control plane");
  }

  // Symblic equality of expressions
  BoolExpr mkEq(Expr e1, Expr e2) {
    return getCtx().mkEq(e1, e2);
  }

  // Add a boolean variable to the model
  void add(BoolExpr e) {
    _unsatCore.track(_solver, _ctx, e);
  }

  /*
   * Adds the constraint that at most k links/nodes have failed.
   * This is done in two steps. First we ensure that each
   * variable that represents a failure is constrained to
   * take on a value between 0 and 1:
   *
   * 0 <= failVar_i <= 1
   *
   * Then we ensure that the sum of all fail variables is never more than k:
   *
   * failVar_1 + failVar_2 + ... + failVar_n <= k
   */
  private void addFailedConstraints(int k, Set<ArithExpr> vars) {
    ArithExpr sum = mkInt(0);
    for (ArithExpr var : vars) {
      sum = mkSum(sum, var);
      add(mkGe(var, mkInt(0)));
      add(mkLe(var, mkInt(1)));
    }
    if (k == 0) {
      for (ArithExpr var : vars) {
        add(mkEq(var, mkInt(0)));
      }
    } else {
      add(mkLe(sum, mkInt(k)));
    }
  }

  /* Generate constraints for link failures */
  private void addFailedLinkConstraints(int k) {
    Set<ArithExpr> vars = new HashSet<>();
    getSymbolicFailures().getFailedInternalLinks().forEach((router, peer, var) -> vars.add(var));
    getSymbolicFailures().getFailedEdgeLinks().forEach((ge, var) -> vars.add(var));
    addFailedConstraints(k, vars);
  }

  /* Generate constraints for node failures */
  private void addFailedNodeConstraints(int k) {
    Set<ArithExpr> vars = new HashSet<>();
    getSymbolicFailures().getFailedNodes().forEach((router, var) -> vars.add(var));
    addFailedConstraints(k, vars);
  }

  /*
   * Check if a community value should be displayed to the human
   */
  private boolean displayCommunity(CommunityVar cvar) {
    if (cvar.getType() == CommunityVar.Type.OTHER) {
      return false;
    }
    if (cvar.getType() == CommunityVar.Type.EXACT) {
      return true;
    }
    return true;
  }

  /*
   * Add the relevant variables in the counterexample to
   * display to the user in a human-readable fashion
   */
  private void buildCounterExample(
      Encoder enc,
      Model m,
      SortedMap<String, String> model,
      SortedMap<String, String> packetModel,
      SortedSet<String> fwdModel,
      SortedMap<String, SortedMap<String, String>> envModel,
      SortedSet<String> failures) {
    SortedMap<Expr, String> valuation = new TreeMap<>();

    // If user asks for the full model
    for (Entry<String, Expr> entry : _allVariables.entrySet()) {
      String name = entry.getKey();
      Expr e = entry.getValue();
      Expr val = m.evaluate(e, true);
      if (!val.equals(e)) {
        String s = val.toString();
        if (_question.getFullModel()) {
          model.put(name, s);
        }
        valuation.put(e, s);
      }
    }

    // Packet model
    SymbolicPacket p = enc.getMainSlice().getSymbolicPacket();
    String dstIp = valuation.get(p.getDstIp());
    String srcIp = valuation.get(p.getSrcIp());
    String dstPt = valuation.get(p.getDstPort());
    String srcPt = valuation.get(p.getSrcPort());
    String icmpCode = valuation.get(p.getIcmpCode());
    String icmpType = valuation.get(p.getIcmpType());
    String ipProtocol = valuation.get(p.getIpProtocol());
    String tcpAck = valuation.get(p.getTcpAck());
    String tcpCwr = valuation.get(p.getTcpCwr());
    String tcpEce = valuation.get(p.getTcpEce());
    String tcpFin = valuation.get(p.getTcpFin());
    String tcpPsh = valuation.get(p.getTcpPsh());
    String tcpRst = valuation.get(p.getTcpRst());
    String tcpSyn = valuation.get(p.getTcpSyn());
    String tcpUrg = valuation.get(p.getTcpUrg());

    Ip dip = Ip.create(Long.parseLong(dstIp));
    Ip sip = Ip.create(Long.parseLong(srcIp));

    packetModel.put("dstIp", dip.toString());

    if (sip.asLong() != 0) {
      packetModel.put("srcIp", sip.toString());
    }
    if (dstPt != null && !dstPt.equals("0")) {
      packetModel.put("dstPort", dstPt);
    }
    if (srcPt != null && !srcPt.equals("0")) {
      packetModel.put("srcPort", srcPt);
    }
    if (icmpCode != null && !icmpCode.equals("0")) {
      packetModel.put("icmpCode", icmpCode);
    }
    if (icmpType != null && !icmpType.equals("0")) {
      packetModel.put("icmpType", icmpType);
    }
    if (ipProtocol != null && !ipProtocol.equals("0")) {
      int number = Integer.parseInt(ipProtocol);
      IpProtocol proto = IpProtocol.fromNumber(number);
      packetModel.put("protocol", proto.toString());
    }
    if ("true".equals(tcpAck)) {
      packetModel.put("tcpAck", "set");
    }
    if ("true".equals(tcpCwr)) {
      packetModel.put("tcpCwr", "set");
    }
    if ("true".equals(tcpEce)) {
      packetModel.put("tcpEce", "set");
    }
    if ("true".equals(tcpFin)) {
      packetModel.put("tcpFin", "set");
    }
    if ("true".equals(tcpPsh)) {
      packetModel.put("tcpPsh", "set");
    }
    if ("true".equals(tcpRst)) {
      packetModel.put("tcpRst", "set");
    }
    if ("true".equals(tcpSyn)) {
      packetModel.put("tcpSyn", "set");
    }
    if ("true".equals(tcpUrg)) {
      packetModel.put("tcpUrg", "set");
    }

    for (EncoderSlice slice : enc.getSlices().values()) {
      for (Entry<LogicalEdge, SymbolicRoute> entry2 :
          slice.getLogicalGraph().getEnvironmentVars().entrySet()) {
        LogicalEdge lge = entry2.getKey();
        SymbolicRoute r = entry2.getValue();
        if ("true".equals(valuation.get(r.getPermitted()))) {
          SortedMap<String, String> recordMap = new TreeMap<>();
          GraphEdge ge = lge.getEdge();
          String nodeIface = ge.getRouter() + "," + ge.getStart().getName() + " (BGP)";
          envModel.put(nodeIface, recordMap);
          if (r.getPrefixLength() != null) {
            String x = valuation.get(r.getPrefixLength());
            if (x != null) {
              int len = Integer.parseInt(x);
              Prefix p1 = Prefix.create(dip, len);
              recordMap.put("prefix", p1.toString());
            }
          }
          if (r.getAdminDist() != null) {
            String x = valuation.get(r.getAdminDist());
            if (x != null) {
              recordMap.put("admin distance", x);
            }
          }
          if (r.getLocalPref() != null) {
            String x = valuation.get(r.getLocalPref());
            if (x != null) {
              recordMap.put("local preference", x);
            }
          }
          if (r.getMetric() != null) {
            String x = valuation.get(r.getMetric());
            if (x != null) {
              recordMap.put("protocol metric", x);
            }
          }
          if (r.getMed() != null) {
            String x = valuation.get(r.getMed());
            if (x != null) {
              recordMap.put("multi-exit disc.", valuation.get(r.getMed()));
            }
          }
          if (r.getOspfArea() != null && r.getOspfArea().getBitVec() != null) {
            String x = valuation.get(r.getOspfArea().getBitVec());
            if (x != null) {
              Integer i = Integer.parseInt(x);
              Long area = r.getOspfArea().value(i);
              recordMap.put("OSPF Area", area.toString());
            }
          }
          if (r.getOspfType() != null && r.getOspfType().getBitVec() != null) {
            String x = valuation.get(r.getOspfType().getBitVec());
            if (x != null) {
              int i = Integer.parseInt(x);
              OspfType type = r.getOspfType().value(i);
              recordMap.put("OSPF Type", type.toString());
            }
          }

          for (Entry<CommunityVar, BoolExpr> entry3 : r.getCommunities().entrySet()) {
            CommunityVar cvar = entry3.getKey();
            BoolExpr e = entry3.getValue();
            String c = valuation.get(e);
            // TODO: what about OTHER type?
            if ("true".equals(c) && displayCommunity(cvar)) {
              String s = cvar.getRegex();
              String t = slice.getNamedCommunities().get(cvar.getRegex());
              s = (t == null ? s : t);
              recordMap.put("community " + s, "");
            }
          }
        }
      }
    }

    // Forwarding Model
    enc.getMainSlice()
        .getSymbolicDecisions()
        .getDataForwarding()
        .forEach(
            (router, edge, e) -> {
              String s = valuation.get(e);
              if ("true".equals(s)) {
                SymbolicRoute r =
                    enc.getMainSlice().getSymbolicDecisions().getBestNeighbor().get(router);
                if (r.getProtocolHistory() != null) {
                  Protocol proto;
                  List<Protocol> allProtocols = enc.getMainSlice().getProtocols().get(router);
                  if (allProtocols.size() == 1) {
                    proto = allProtocols.get(0);
                  } else {
                    s = valuation.get(r.getProtocolHistory().getBitVec());
                    int i = Integer.parseInt(s);
                    proto = r.getProtocolHistory().value(i);
                  }
                  fwdModel.add(edge + " (" + proto.name() + ")");
                } else {
                  fwdModel.add(edge.toString());
                }
              }
            });

    _symbolicFailures
        .getFailedInternalLinks()
        .forEach(
            (x, y, e) -> {
              String s = valuation.get(e);
              if ("1".equals(s)) {
                String pair = (x.compareTo(y) < 0 ? x + "," + y : y + "," + x);
                failures.add("link(" + pair + ")");
              }
            });

    _symbolicFailures
        .getFailedEdgeLinks()
        .forEach(
            (ge, e) -> {
              String s = valuation.get(e);
              if ("1".equals(s)) {
                failures.add("link(" + ge.getRouter() + "," + ge.getStart().getName() + ")");
              }
            });

    _symbolicFailures
        .getFailedNodes()
        .forEach(
            (x, e) -> {
              String s = valuation.get(e);
              if ("1".equals(s)) {
                failures.add("node(" + x + ")");
              }
            });
  }

  /*
   * Generate a blocking clause for the encoding that says that one
   * of the environments that was true before must now be false.
   */
  private BoolExpr environmentBlockingClause(Model m) {
    BoolExpr acc1 = mkFalse();
    BoolExpr acc2 = mkTrue();

    // Disable an environment edge if possible
    Map<LogicalEdge, SymbolicRoute> map = getMainSlice().getLogicalGraph().getEnvironmentVars();
    for (Map.Entry<LogicalEdge, SymbolicRoute> entry : map.entrySet()) {
      SymbolicRoute record = entry.getValue();
      BoolExpr per = record.getPermitted();
      Expr x = m.evaluate(per, false);
      if (x.toString().equals("true")) {
        acc1 = mkOr(acc1, mkNot(per));
      } else {
        acc2 = mkAnd(acc2, mkNot(per));
      }
    }

    // Disable a community value if possible
    for (Map.Entry<LogicalEdge, SymbolicRoute> entry : map.entrySet()) {
      SymbolicRoute record = entry.getValue();
      for (Map.Entry<CommunityVar, BoolExpr> centry : record.getCommunities().entrySet()) {
        BoolExpr comm = centry.getValue();
        Expr x = m.evaluate(comm, false);
        if (x.toString().equals("true")) {
          acc1 = mkOr(acc1, mkNot(comm));
        } else {
          acc2 = mkAnd(acc2, mkNot(comm));
        }
      }
    }

    return mkAnd(acc1, acc2);
  }

  /**
   * Checks that a property is always true by seeing if the encoding is unsatisfiable. If the model
   * is satisfiable, then there is a counter example to the property.
   *
   * @return A VerificationResult indicating the status of the check.
   */
  public Tuple<VerificationResult, Model> verify() {

    EncoderSlice mainSlice = _slices.get(MAIN_SLICE_NAME);

    // count the number of smt variable and constraint
    int numVariables = _allVariables.size();
    int numConstraints = _solver.getAssertions().length;
    // count the number of network node and edge according to main encoder slice
    int numNodes = mainSlice.getGraph().getConfigurations().size();
    int numEdges = 0;
    for (Map.Entry<String, Set<String>> e : mainSlice.getGraph().getNeighbors().entrySet()) {
      numEdges += e.getValue().size();
    }

    // simplify all assertions and record in simplifiedSolver
    Solver simplifiedSolver = _ctx.mkSolver();
    for (BoolExpr assertion : _solver.getAssertions()) {
      BoolExpr simplifiedAssertion = (BoolExpr) assertion.simplify();
      simplifiedSolver.add(simplifiedAssertion);
    }

    // System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
    // System.out.println(simplifiedSolver.toString());
    _smtWriter.println(simplifiedSolver.toString());
    _smtWriter.println("(check-sat)");
    _smtWriter.println("(get-model)");
    _smtWriter.close();
    // System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");

    long start = System.currentTimeMillis();
    Status status = _solver.check();
    long time = System.currentTimeMillis() - start;

    VerificationStats stats = null;
    if (_question.getBenchmark()) {
      stats = new VerificationStats();
      stats.setAvgNumNodes(numNodes);
      stats.setMaxNumNodes(numNodes);
      stats.setMinNumNodes(numNodes);
      stats.setAvgNumEdges(numEdges);
      stats.setMaxNumEdges(numEdges);
      stats.setMinNumEdges(numEdges);
      stats.setAvgNumVariables(numVariables);
      stats.setMaxNumVariables(numVariables);
      stats.setMinNumVariables(numVariables);
      stats.setAvgNumConstraints(numConstraints);
      stats.setMaxNumConstraints(numConstraints);
      stats.setMinNumConstraints(numConstraints);
      stats.setAvgSolverTime(time);
      stats.setMaxSolverTime(time);
      stats.setMinSolverTime(time);
    }

    if (status == Status.UNSATISFIABLE) {
      VerificationResult res = new VerificationResult(true, null, null, null, null, null, stats);
      return new Tuple<>(res, null);
    } else if (status == Status.UNKNOWN) {
      throw new BatfishException("ERROR: satisfiability unknown");
    } else {
      VerificationResult result;

      Model m;
      while (true) {
        m = _solver.getModel();
        SortedMap<String, String> model = new TreeMap<>();
        SortedMap<String, String> packetModel = new TreeMap<>();
        SortedSet<String> fwdModel = new TreeSet<>();
        SortedMap<String, SortedMap<String, String>> envModel = new TreeMap<>();
        SortedSet<String> failures = new TreeSet<>();
        buildCounterExample(this, m, model, packetModel, fwdModel, envModel, failures);
        if (_previousEncoder != null) {
          buildCounterExample(
              _previousEncoder, m, model, packetModel, fwdModel, envModel, failures);
        }

        result =
            new VerificationResult(false, model, packetModel, envModel, fwdModel, failures, stats);

        if (!_question.getMinimize()) {
          break;
        }

        BoolExpr blocking = environmentBlockingClause(m);
        add(blocking);

        Status s = _solver.check();
        if (s == Status.UNSATISFIABLE) {
          break;
        }
        if (s == Status.UNKNOWN) {
          throw new BatfishException("ERROR: satisfiability unknown");
        }
      }

      return new Tuple<>(result, m);
    }
  }

  /**
   * Adds all the constraints to capture the interactions of messages among all protocols in the
   * network. This should be called prior to calling the <b>verify method</b>
   */
  void computeEncoding() {
    if (_graph.hasStaticRouteWithDynamicNextHop()) {
      throw new BatfishException(
          "Cannot encode a network that has a static route with a dynamic next hop");
    }

    addFailedLinkConstraints(_question.getFailures());
    addFailedNodeConstraints(_question.getNodeFailures());

    // addEnvironmentVariables
    getMainSlice().computeEncoding();

    for (Entry<String, EncoderSlice> entry : _slices.entrySet()) {
      String name = entry.getKey();
      EncoderSlice slice = entry.getValue();
      if (!name.equals(MAIN_SLICE_NAME)) {
        slice.computeEncoding();
      }
    }
  }

  private void initOutput() {
    _outputDirectoryName = createOutputDirectory();

    String outputSmtFileName = _outputDirectoryName + "/smt_encoding.smt2";
    String outputConstFileName = _outputDirectoryName + "/config_constraints.smt2";
    String outputConfigFileName = _outputDirectoryName + "/configs_to_variables.txt";

    File outputSmtFile = new File(outputSmtFileName);
    File outputConstFile = new File(outputConstFileName);
    File outputConfigFile = new File(outputConfigFileName);

    try {
      _smtWriter = new PrintWriter(new FileWriter(outputSmtFile, true));
      _constWriter = new PrintWriter(new FileWriter(outputConstFile, true));
      _configWriter = new PrintWriter(new FileWriter(outputConfigFile, true));
    } catch (IOException e) {
      System.err.println("Error: Unable to create file: " + e.getMessage());
    }
  }

  private static String createOutputDirectory() {
    // SMT_DIRECTORY_PREFIX = "/PATH-TO/batfish/smts"
    final String DIRECTORY_PREFIX = System.getenv("SMT_DIRECTORY_PREFIX");
    final String DIRECTORY_NAME = DIRECTORY_PREFIX + "/smt_output_";
    final int DIRECTORY_INDEX_LIMIT = 9999;

    String outputDirectoryName = null;

    for (int i = 1; i <= DIRECTORY_INDEX_LIMIT; ++i) {
      // outputDirectoryName = "/PATH-TO/batfish/smts/smt_output_xxxx"
      // output directory range from 0001 to 9999
      outputDirectoryName = String.format("%s%04d", DIRECTORY_NAME, i);
      File outputDirectory = new File(outputDirectoryName);

      if (outputDirectory.exists()) {
        continue;
      }

      try {
        outputDirectory.mkdir();
      } catch (SecurityException e) {
        System.err.println("Error: Unable to create directory: " + e.getMessage());
      }

      break;
    }

    return outputDirectoryName;
  }

  /*
   * Getters and setters
   */

  SymbolicFailures getSymbolicFailures() {
    return _symbolicFailures;
  }

  EncoderSlice getSlice(String router) {
    String s = "SLICE-" + router + "_";
    return _slices.get(s);
  }

  public Context getCtx() {
    return _ctx;
  }

  EncoderSlice getMainSlice() {
    return _slices.get(MAIN_SLICE_NAME);
  }

  Solver getSolver() {
    return _solver;
  }

  Map<String, Expr> getAllVariables() {
    return _allVariables;
  }

  int getId() {
    return _encodingId;
  }

  boolean getModelIgp() {
    return _modelIgp;
  }

  Map<String, Map<String, BoolExpr>> getSliceReachability() {
    return _sliceReachability;
  }

  UnsatCore getUnsatCore() {
    return _unsatCore;
  }

  int getFailures() {
    return _question.getFailures();
  }

  public boolean getFullModel() {
    return _question.getFullModel();
  }

  private Map<String, EncoderSlice> getSlices() {
    return _slices;
  }

  HeaderQuestion getQuestion() {
    return _question;
  }

  public String getDirectoryName() {
    return _outputDirectoryName;
  }

  public void setQuestion(HeaderQuestion question) {
    _question = question;
  }

  public BitVecExpr mkBV(long val, int size) {
    return _ctx.mkBV(val, size);
  }

  public BitVecExpr mkBVAND(BitVecExpr expr, BitVecExpr mask) {
    return _ctx.mkBVAND(expr, mask);
  }

  public ArithExpr mkIntConst(String name) {
    return _ctx.mkIntConst(name);
  }

  public BitVecExpr mkBVConst(String name, int size) {
    return _ctx.mkBVConst(name, size);
  }

  private static String format(String str) {
    String formatedStr = "";

    // replace some characters with '_'
    for (char c : str.toCharArray()) {
      switch (c) {
        case '~':
        case '-':
        case ':':
        case '.':
        case '/':
          formatedStr += '_';
          break;
        default:
          formatedStr += c;
          break;
      }
    }

    // remove the start with '_'
    if (formatedStr.startsWith("_")) {
      formatedStr = formatedStr.substring(1);
    }
    // remove the end with '_'
    if (formatedStr.endsWith("_")) {
      formatedStr = formatedStr.substring(0, formatedStr.length() - 1);
    }

    return formatedStr;
  }

  public static String incrementLineSuffix(String routingPolicyLineName) {
    // match end with "_LineN" (N is integer number)
    String pattern = "(.+)__Line(\\d+)__$";
    java.util.regex.Pattern r = java.util.regex.Pattern.compile(pattern);
    java.util.regex.Matcher m = r.matcher(routingPolicyLineName);

    if (m.matches()) {
      String prefix = m.group(1);
      int number = Integer.parseInt(m.group(2));
      return prefix + "__Line" + (number + 1) + "__";
    } else {
      return routingPolicyLineName + "_Line1__";
    }
  }

  private static String longToIpString(long ip) {
    return String.format(
        "%d.%d.%d.%d",
        (ip >> 24) & 0xFF,
        (ip >> 16) & 0xFF,
        (ip >> 8) & 0xFF,
        ip & 0xFF
    );
  }

  private void initConfigurationConstants() {
    for (Map.Entry<String, Configuration> configEntry : _graph.getConfigurations().entrySet()) {
      String hostName = configEntry.getKey();
      Configuration config = configEntry.getValue();

      // write host name to configs_to_variables file
      _configWriter.println(hostName);

      for (Map.Entry<String, RouteFilterList> routeFilterListEntry : config.getRouteFilterLists().entrySet()) {
        String routerFilterListName = routeFilterListEntry.getKey();
        RouteFilterList routeFilterList = routeFilterListEntry.getValue();
        List<RouteFilterLine> lines = routeFilterList.getLines();

        // exclude other router filter list with configuration constants -> SMT symbolic variables
        // if (routerFilterListName.contains("default")) {
        //   continue;
        // }

        // write route filter list name to configs_to_variables file
        _configWriter.println("  * " + "ip prefix-list / access-list: " + routerFilterListName);

        for (RouteFilterLine line : lines) {
          long prefixIp = line.getIpWildcard().getIp().asLong();
          String prefixIpStr = longToIpString(prefixIp);
          String configVarPrefix =
              "Config_" + hostName + "_RouteFilterList_" + format(routerFilterListName) +
              "__" + format(prefixIpStr) + "__";
          line.initSmtVariable(_ctx, _solver, configVarPrefix);

          // write (ipLongFormat -> ipStringFormat) to configs_to_variables file
          _configWriter.println("    (" + prefixIp + " -> " + prefixIpStr + ")");
          // write smt symbolic variable name to configs_to_variables file
          // RouteFilterList
          _configWriter.println("    + " + configVarPrefix + "action");
          // IpWildcard
          _configWriter.println("    + " + configVarPrefix + "ip");
          _configWriter.println("    + " + configVarPrefix + "mask");
          _configWriter.println("    + " + configVarPrefix + "length");
          // SubRange
          _configWriter.println("    + " + configVarPrefix + "prefix_range_start");
          _configWriter.println("    + " + configVarPrefix + "prefix_range_end");
        }
      }

      for (Map.Entry<String, RoutingPolicy> routingPolicyEntry : config.getRoutingPolicies().entrySet()) {
        String policyName = routingPolicyEntry.getKey();
        RoutingPolicy routingPolicy = routingPolicyEntry.getValue();

        // exclude other routing policy with configuration constants -> SMT symbolic variables
        // if (policyName.contains("default")) {
        //   continue;
        // }

        // TODO: write smt symbolic variable name to configs_to_variables file
        //       annotated by yongzheng on 20250407
        _configWriter.println("  * " + "routing policy (todo): " + policyName);

        List<Statement> statements = routingPolicy.getStatements();
        initConfigurationConstants(
            statements, "Config_" + hostName + "_RoutingPolicy_" + format(policyName) + "_");
      }
    }


    // System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
    // System.out.println(_solver.toString());
    _constWriter.println(_solver.toString());
    _constWriter.close();
    // System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    _configWriter.close();
  }

  private void initConfigurationConstants(
      List<Statement> statements, String configVarPrefix) {
    for (Statement stmt : statements) {
      if (stmt instanceof StaticStatement) {
        // TODO: check here and implement it when needed
        StaticStatement ss = (StaticStatement) stmt;
        switch (ss.getType()) {
          case ExitAccept:
            break;
          case Unsuppress:
          case ReturnTrue:
            break;
          case ExitReject:
            break;
          case Suppress:
          case ReturnFalse:
            break;
          case SetDefaultActionAccept:
            break;
          case SetDefaultActionReject:
            break;
          case SetLocalDefaultActionAccept:
            break;
          case SetLocalDefaultActionReject:
            break;
          case ReturnLocalDefaultAction:
            break;
          case FallThrough:
            break;
          case Return:
            break;
          case RemovePrivateAs:
            break;
          default:
            String msg = String.format("Unimplemented feature %s", ss.getType());
            throw new BatfishException(msg);
        }

      } else if (stmt instanceof If) {
        // IF
        //   guard
        // THEN
        //   trueStatements
        // ELSE
        //   falseStatement
        If i = (If) stmt;
        configVarPrefix = incrementLineSuffix(configVarPrefix);
        initConfigurationConstants(i.getGuard(), configVarPrefix);
        initConfigurationConstants(i.getTrueStatements(), configVarPrefix);
        initConfigurationConstants(i.getFalseStatements(), configVarPrefix);

      } else if (stmt instanceof SetDefaultPolicy) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof SetMetric) {
        SetMetric sm = (SetMetric) stmt;
        sm.initSmtVariable(_ctx, _solver, configVarPrefix + "set_metric");

      } else if (stmt instanceof SetOspfMetricType) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof SetLocalPreference) {
        SetLocalPreference slp = (SetLocalPreference) stmt;
        slp.initSmtVariable(_ctx, _solver, configVarPrefix + "set_localpreference");

      } else if (stmt instanceof AddCommunity) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof SetCommunity) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof DeleteCommunity) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof PrependAsPath) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof SetOrigin) {
        // TODO: implement me
        {}  // do nothing

      } else if (stmt instanceof SetNextHop) {
        // TODO: implement me
        {}  // do nothing

      } else {
        String msg = String.format("Unimplemented feature %s", stmt.toString());
        throw new BatfishException(msg);
      }
    }
  }

  private void initConfigurationConstants(BooleanExpr expr, String configVarPrefix) {
    if (expr instanceof MatchIpv4) {
      // TODO: implement me
      {}  // do nothing
    }

    if (expr instanceof MatchIpv6) {
      // TODO: implement me
      {}  // do nothing
    }

    if (expr instanceof Conjunction) {
      Conjunction c = (Conjunction) expr;
      for (BooleanExpr booleanExpr : c.getConjuncts()) {
        initConfigurationConstants(booleanExpr, configVarPrefix);
      }
    }

    if (expr instanceof Disjunction) {
      Disjunction d = (Disjunction) expr;
      for (BooleanExpr booleanExpr : d.getDisjuncts()) {
        initConfigurationConstants(booleanExpr, configVarPrefix);
      }
    }

    if (expr instanceof ConjunctionChain) {
      // TODO: check here
      ConjunctionChain d = (ConjunctionChain) expr;
      List<BooleanExpr> conjuncts = new ArrayList<>(d.getSubroutines());
      for (BooleanExpr booleanExpr : conjuncts) {
        initConfigurationConstants(booleanExpr, configVarPrefix);
      }
    }

    if (expr instanceof FirstMatchChain) {
      // TODO: check here
      FirstMatchChain chain = (FirstMatchChain) expr;
      List<BooleanExpr> chainPolicies = new ArrayList<>(chain.getSubroutines());
      for (BooleanExpr booleanExpr : chainPolicies) {
        initConfigurationConstants(booleanExpr, configVarPrefix);
      }
    }

    if (expr instanceof Not) {
      // TODO: check here
      Not n = (Not) expr;
      initConfigurationConstants(n.getExpr(), configVarPrefix);
    }

    if (expr instanceof MatchProtocol) {
      // FIXME: check here and implement it when needed
      MatchProtocol mp = (MatchProtocol) expr;
      Set<RoutingProtocol> rps = mp.getProtocols();
      if (rps.size() > 1) {
        // Hack: Minesweeper doesn't support MatchProtocol with multiple arguments.
        List<BooleanExpr> mps = rps.stream().map(MatchProtocol::new).collect(Collectors.toList());
        for (BooleanExpr booleanExpr : mps) {
          initConfigurationConstants(booleanExpr, configVarPrefix);
        }
      }
    }

    if (expr instanceof MatchPrefixSet) {
      // TODO: check here and implement it when needed
      MatchPrefixSet mps = (MatchPrefixSet) expr;
      mps.initSmtVariable(_ctx, _solver, configVarPrefix);

      // write smt symbolic variables name to configs_to_variables file
      PrefixSetExpr prefixSetExpr = mps.getPrefixSet();
      if (prefixSetExpr instanceof ExplicitPrefixSet) {
        ExplicitPrefixSet eps = (ExplicitPrefixSet) prefixSetExpr;
        for (PrefixRange prefixRange : eps.getPrefixSpace().getPrefixRanges()) {
          // write (ipLongFormat -> ipStringFormat) to configs_to_variables file
          long prefixIp = prefixRange.getPrefix().getStartIp().asLong();
          String prefixIpStr = longToIpString(prefixIp);
          _configWriter.println("    (" + prefixIp + " -> " + prefixIpStr + ")");
          // write smt symbolic variable name to configs_to_variables file
          _configWriter.println("    + " + configVarPrefix + "_" + format(prefixIpStr) + "__ip");
          _configWriter.println("    + " + configVarPrefix + "_" + format(prefixIpStr) + "__mask");
          _configWriter.println(
              "    + " + configVarPrefix + "_" + format(prefixIpStr) + "__length");
          _configWriter.println(
              "    + " + configVarPrefix + "_" + format(prefixIpStr) + "__prefix_range_start");
          _configWriter.println(
              "    + " + configVarPrefix + "_" + format(prefixIpStr) + "__prefix_range_end");
        }
      } else if (prefixSetExpr instanceof NamedPrefixSet) {
        // call ip prefix-list / access-list
      }

    } else if (expr instanceof MatchPrefix6Set) {
      // TODO: implement me
      {}  // do nothing

    } else if (expr instanceof CallExpr) {
      // TODO: check here and implement it when needed
      CallExpr ce = (CallExpr) expr;
      _configWriter.println("    + " + "call " + ce.getCalledPolicyName());

    } else if (expr instanceof WithEnvironmentExpr) {
      WithEnvironmentExpr we = (WithEnvironmentExpr) expr;
      initConfigurationConstants(we.getExpr(), configVarPrefix);

    } else if (expr instanceof MatchCommunitySet) {
      // TODO: check here and implement it when needed
      {}  // do nothing

    } else if (expr instanceof BooleanExprs.StaticBooleanExpr) {
      BooleanExprs.StaticBooleanExpr b = (BooleanExprs.StaticBooleanExpr) expr;
      switch (b.getType()) {
        case CallExprContext:
          break;
        case CallStatementContext:
          break;
        case True:
          break;
        case False:
          break;
        default:
          // FIXME: check here and implement it when needed
          // String msg = String.format(
          //     "Unimplemented feature %s : %s", BooleanExprs.class.getCanonicalName(), b.getType());
          // throw new BatfishException(msg);
          break;
      }

    } else if (expr instanceof MatchAsPath) {
      // TODO: implement me
      {}  // do nothing
    }

    // FIXME: check here and implement it when needed
    // String msg = String.format("Unimplemented feature %s", expr.toString());
    // throw new BatfishException(msg);
  }
}