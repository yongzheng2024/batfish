package org.batfish.minesweeper.bddsmt;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.JFactory;
import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
// import org.batfish.common.BatfishException;
import org.batfish.datamodel.AsPathAccessList;
import org.batfish.datamodel.AsPathAccessListLine;
import org.batfish.datamodel.Configuration;
// import org.batfish.datamodel.Ip;
import org.batfish.datamodel.LineAction;
// import org.batfish.datamodel.OriginType;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.RouteFilterList;
// import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.SubRange;
// import org.batfish.datamodel.ospf.OspfMetricType;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
// import org.batfish.datamodel.routing_policy.as_path.InputAsPath;
// import org.batfish.datamodel.routing_policy.as_path.MatchAsPath;
// import org.batfish.datamodel.routing_policy.communities.InputCommunities;
// import org.batfish.datamodel.routing_policy.communities.MatchCommunities;
import org.batfish.datamodel.routing_policy.communities.SetCommunities;
import org.batfish.datamodel.routing_policy.communities.CommunitySetExpr;
// import org.batfish.datamodel.routing_policy.expr.AsExpr;
// import org.batfish.datamodel.routing_policy.expr.AsPathListExpr;
import org.batfish.datamodel.routing_policy.expr.AsPathSetExpr;
// import org.batfish.datamodel.routing_policy.expr.BgpPeerAddressNextHop;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
// import org.batfish.datamodel.routing_policy.expr.BooleanExprs;
// import org.batfish.datamodel.routing_policy.expr.CallExpr;
import org.batfish.datamodel.routing_policy.expr.Conjunction;
// import org.batfish.datamodel.routing_policy.expr.ConjunctionChain;
import org.batfish.datamodel.routing_policy.expr.DestinationNetwork;
// import org.batfish.datamodel.routing_policy.expr.DiscardNextHop;
// import org.batfish.datamodel.routing_policy.expr.Disjunction;
// import org.batfish.datamodel.routing_policy.expr.ExplicitAs;
import org.batfish.datamodel.routing_policy.expr.ExplicitPrefixSet;
// import org.batfish.datamodel.routing_policy.expr.FirstMatchChain;
import org.batfish.datamodel.routing_policy.expr.IncrementMetric;
// import org.batfish.datamodel.routing_policy.expr.IntComparator;
// import org.batfish.datamodel.routing_policy.expr.IntExpr;
// import org.batfish.datamodel.routing_policy.expr.IpNextHop;
import org.batfish.datamodel.routing_policy.expr.IpPrefix;
import org.batfish.datamodel.routing_policy.expr.LegacyMatchAsPath;
// import org.batfish.datamodel.routing_policy.expr.LiteralAsList;
import org.batfish.datamodel.routing_policy.expr.LiteralInt;
import org.batfish.datamodel.routing_policy.expr.LiteralLong;
// import org.batfish.datamodel.routing_policy.expr.LiteralOrigin;
// import org.batfish.datamodel.routing_policy.expr.LiteralTunnelEncapsulationAttribute;
import org.batfish.datamodel.routing_policy.expr.LongExpr;
// import org.batfish.datamodel.routing_policy.expr.MatchClusterListLength;
// import org.batfish.datamodel.routing_policy.expr.MatchInterface;
import org.batfish.datamodel.routing_policy.expr.MatchIpv4;
// import org.batfish.datamodel.routing_policy.expr.MatchMetric;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
// import org.batfish.datamodel.routing_policy.expr.MatchProtocol;
// import org.batfish.datamodel.routing_policy.expr.MatchSourceVrf;
// import org.batfish.datamodel.routing_policy.expr.MatchTag;
import org.batfish.datamodel.routing_policy.expr.NamedAsPathSet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
// import org.batfish.datamodel.routing_policy.expr.NextHopExpr;
import org.batfish.datamodel.routing_policy.expr.NextHopIp;
import org.batfish.datamodel.routing_policy.expr.Not;
// import org.batfish.datamodel.routing_policy.expr.OriginExpr;
import org.batfish.datamodel.routing_policy.expr.PrefixExpr;
import org.batfish.datamodel.routing_policy.expr.PrefixSetExpr;
// import org.batfish.datamodel.routing_policy.expr.SelfNextHop;
// import org.batfish.datamodel.routing_policy.expr.TrackSucceeded;
// import org.batfish.datamodel.routing_policy.expr.WithEnvironmentExpr;
// import org.batfish.datamodel.routing_policy.statement.CallStatement;
import org.batfish.datamodel.routing_policy.statement.If;
// import org.batfish.datamodel.routing_policy.statement.PrependAsPath;
// import org.batfish.datamodel.routing_policy.statement.RemoveTunnelEncapsulationAttribute;
// import org.batfish.datamodel.routing_policy.statement.SetAdministrativeCost;
// import org.batfish.datamodel.routing_policy.statement.SetDefaultPolicy;
import org.batfish.datamodel.routing_policy.statement.SetLocalPreference;
// import org.batfish.datamodel.routing_policy.statement.SetMetric;
// import org.batfish.datamodel.routing_policy.statement.SetNextHop;
// import org.batfish.datamodel.routing_policy.statement.SetOrigin;
// import org.batfish.datamodel.routing_policy.statement.SetOspfMetricType;
// import org.batfish.datamodel.routing_policy.statement.SetTag;
// import org.batfish.datamodel.routing_policy.statement.SetTunnelEncapsulationAttribute;
// import org.batfish.datamodel.routing_policy.statement.SetWeight;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements.StaticStatement;
import org.batfish.datamodel.routing_policy.statement.TraceableStatement;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
// import org.batfish.minesweeper.OspfType;
import org.batfish.minesweeper.RegexAtomicPredicates;
import org.batfish.minesweeper.SymbolicAsPathRegex;
import org.batfish.minesweeper.SymbolicRegex;
// import org.batfish.minesweeper.bdd.BDDTunnelEncapsulationAttribute.Value;
// import org.batfish.minesweeper.bdd.CommunitySetMatchExprToBDD.Arg;
import org.batfish.minesweeper.bddsmt.CommunitySetMatchExprToBDD.Arg;

import org.batfish.common.bddsmt.BDDSMT;
import org.batfish.common.bddsmt.MutableBDDSMTInteger;

import com.microsoft.z3.Context;
import com.microsoft.z3.BoolExpr;


/**
 * @author Ryan Beckett
 */
public class TransferBDDSMT {

  private static final Logger LOGGER = LogManager.getLogger(TransferBDDSMT.class);

  /**
   * We track community and AS-path regexes by computing a set of atomic predicates for them. See
   * {@link org.batfish.minesweeper.RegexAtomicPredicates}. During the symbolic route analysis, we
   * simply need the map from each regex to its corresponding set of atomic predicates, each
   * represented by a unique integer.
   */
  private final Map<CommunityVar, Set<Integer>> _communityAtomicPredicates;

  private final Map<SymbolicAsPathRegex, Set<Integer>> _asPathRegexAtomicPredicates;

  private final Configuration _conf;

  private final RoutingPolicy _policy;

  private final ConfigAtomicPredicates _configAtomicPredicates;

  private final List<Statement> _statements;

  private final BDDSMTRoute _originalRoute;

  private final boolean _useOutputAttributes;

  private final BDDFactory _factory;

  private final Context _context;

  private final Set<String> _unsupportedAlreadyWarned;

  // smt expression count
  private long _exprIndex;

  // a summary about smt expression prefix name
  // actual prefix name needs to be added smt expression count EXPR_INDEX;
  private static final String ACTION_PERMIT = "action_premit_";
  private static final String MATCH_PREFIX_SET = "match_prefix_set_";
  private static final String MATCH_PREFIX_IP = "match_prefix_ip_";
  private static final String MATCH_PREFIX_LENGTH = "match_prefix_length_";
  private static final String MATCH_NEXTHOP_IP = "match_nexthop_ip_";
  private static final String MATCH_ASPATH_REGEXES = "match_aspath_regexes_";
  private static final String MATCH_ASPATH_ACCESSLIST = "match_aspatch_accesslist_";
  private static final String MATCH_FILTER_LIST = "match_filter_list_"; 
  private static final String UNMATCHED = "unmatched_";

  public TransferBDDSMT(ConfigAtomicPredicates aps, RoutingPolicy policy) {
    this(JFactory.init(100000, 10000), new Context(), aps, policy);
  }

  public TransferBDDSMT(
      BDDFactory factory, Context context, ConfigAtomicPredicates aps, RoutingPolicy policy) {
    _configAtomicPredicates = aps;
    _policy = policy;
    _conf = policy.getOwner();
    _statements = policy.getStatements();
    _useOutputAttributes = Environment.useOutputAttributesFor(_conf);
    _unsupportedAlreadyWarned = new HashSet<>();

    _factory = factory;
    _factory.setCacheRatio(64);

    _context = context;

    _originalRoute = new BDDSMTRoute(_factory, _context, aps);
    RegexAtomicPredicates<CommunityVar> standardCommAPs =
        _configAtomicPredicates.getStandardCommunityAtomicPredicates();
    _communityAtomicPredicates = new HashMap<>(standardCommAPs.getRegexAtomicPredicates());
    // add the atomic predicates for the extended/large community literals
    _configAtomicPredicates
        .getNonStandardCommunityLiterals()
        .forEach((key, value) -> _communityAtomicPredicates.put(value, ImmutableSet.of(key)));
    _asPathRegexAtomicPredicates =
        _configAtomicPredicates.getAsPathRegexAtomicPredicates().getRegexAtomicPredicates();

    // initialize smt variable count
    _exprIndex = 0;
  }

  /**
   * The results of symbolic route-map analysis: one {@link
   * org.batfish.minesweeper.bdd.TransferReturn} per execution path through the given route map. The
   * list of paths is unordered, and by construction each path is unique, as each path has a unique
   * condition under which it is taken (the BDD in the TransferResult). The particular statements
   * executed along a given path are not included in this representation but can be reconstructed by
   * simulating one route that takes this path using {@link
   * org.batfish.question.testroutepolicies.TestRoutePoliciesQuestion}.
   */
  public List<TransferBDDSMTReturn> computePaths() {
    BDDSMTRoute o = new BDDSMTRoute(_factory, _context, _configAtomicPredicates);
    // NOTE: modified by yongzheng to enable debug information in TransferBDDSMTParam
    // TransferBDDSMTParam p = new TransferBDDSMTParam(o, false);
    TransferBDDSMTParam p = new TransferBDDSMTParam(o, true);
    return computePaths(_statements, p)
        .stream().map(TransferBDDSMTResult::getReturnValue)
        .collect(ImmutableList.toImmutableList());
  }

  /**
   * Symbolic analysis of a list of route-policy statements. Returns one TransferResult per path
   * through the list of statements. The list of paths is unordered, and by construction each path
   * is unique, as each path has a unique condition under which it is taken (the BDD in the
   * TransferResult). The particular statements executed along a given path are not included in this
   * representation but can be reconstructed by simulating one route that takes this path using
   * {@link org.batfish.question.testroutepolicies.TestRoutePoliciesQuestion}.
   */
  private List<TransferBDDSMTResult> computePaths(
      List<Statement> statements, TransferBDDSMTParam p) {
    TransferBDDSMTParam curP = p;
    TransferBDDSMTResult result = new TransferBDDSMTResult(curP.getData());

    List<TransferBDDSMTState> states =
        compute(statements, ImmutableList.of(new TransferBDDSMTState(curP, result)));

    ImmutableList.Builder<TransferBDDSMTResult> results = ImmutableList.builder();

    for (TransferBDDSMTState state : states) {
      curP = state.getTransferParam();      // return TransferBDDSMTParam
      result = state.getTransferResult();   // return TransferBDDSMTResult

      // Ignore infeasible paths
      if (result.getReturnValue().getInputConstraints().isZero()) {
        continue;
      }

      curP.debug("InitialCall finalizing");

      // Only accept routes that are not suppressed
      if (result.getSuppressedValue()) {
        result = result.setReturnValueAccepted(false);
      }

      results.add(result);
    }

    return results.build();
  }

  /*
   * Symbolic analysis of a list of route-policy statements.
   * Produces one TransferBDDState per path through the given list of statements.
   */
  private List<TransferBDDSMTState> compute(
      List<Statement> statements, List<TransferBDDSMTState> states) {
    List<TransferBDDSMTState> currStates = states;
    for (Statement stmt : statements) {
      List<TransferBDDSMTState> newStates = new ArrayList<>();
      for (TransferBDDSMTState currState : currStates) {
        try {
          if (unreachable(currState.getTransferResult())) {
            // if the path has already reached an exit/return then just keep it
            newStates.add(currState);
          } else {
            // otherwise symbolically execute the next statement
            newStates.addAll(compute(stmt, currState));
          }
        } catch (UnsupportedOperationException e) {
          unsupported(e, currState.getTransferParam().getData());
          newStates.add(currState);
        }
      }
      currStates = newStates;
    }
    return currStates;
  }

  /**
   * Produces one TransferResult per path through the given boolean expression. For most
   * expressions, for example matching on a prefix or community, this analysis will yield exactly
   * two paths, respectively representing the case when the expression evaluates to true and false.
   * Some expressions, such as CallExpr, Conjunction, and Disjunction, implicitly or explicitly
   * contain branches and so can yield more than two paths.
   * TODO: Any updates to the TransferParam in expr are lost currently.
   */
  private List<TransferBDDSMTResult> compute(BooleanExpr expr, TransferBDDSMTState state)
      throws UnsupportedOperationException {

    TransferBDDSMTParam p = state.getTransferParam();
    TransferBDDSMTResult result = state.getTransferResult();

    List<TransferBDDSMTResult> finalResults = new ArrayList<>();

    // TODO: right now everything is IPv4
    if (expr instanceof MatchIpv4) {
      p.debug("MatchIpv4 Result: true");
      // method 1, use routeForMatching to get current BDDSMTRoute, then get Context
      // method 2, directly use Context object _context
      // NOTE: currently adopt method 2
      // Context bddsmtContext = routeForMatching(p).getContext();
      // TransferBDDSMTResult bddsmtResult = 
      //     result.setReturnValueBDDSMT(_factory.one(), bddsmtContext.mkTrue());
      TransferBDDSMTResult bddsmtResult = 
          result.setReturnValueBDDSMT(_factory.one(), _context.mkTrue());
      finalResults.add(bddsmtResult.setReturnValueAccepted(true));

    // Not aBoolExpr -> ! compute(aBoolExpr, state)
    } else if (expr instanceof Not) {
      p.debug("mkNot");
      Not n = (Not) expr;
      List<TransferBDDSMTResult> results = compute(n.getExpr(), state);
      for (TransferBDDSMTResult currResult : results) {
        TransferBDDSMTResult bddsmtResult = 
            currResult.setReturnValueAccepted(!currResult.getReturnValue().getAccepted());
        finalResults.add(bddsmtResult);
      }

    // Conjunction aBoolExpr bBoolExpr ... -> aBoolExpr /\ bBoolExpr /\ ...
    } else if (expr instanceof Conjunction) {
      Conjunction conj = (Conjunction) expr;
      List<TransferBDDSMTResult> currResults = new ArrayList<>();
      // the default result is true
      TransferBDDSMTResult bddsmtResult = 
          result.setReturnValueBDDSMT(_factory.one(), _context.mkTrue());
      currResults.add(bddsmtResult.setReturnValueAccepted(true));
      for (BooleanExpr e : conj.getConjuncts()) {
        List<TransferBDDSMTResult> nextResults = new ArrayList<>();
        try {
          for (TransferBDDSMTResult curr : currResults) {
            BDD currBdd = curr.getReturnValue().getInputConstraints();
            BoolExpr currSmt = curr.getReturnValue().getInputSmtConstraints();
            compute(e, toTransferBDDSMTState(p.indent(), curr)).forEach(
                res -> {
                    TransferBDDSMTReturn updatedReturn = res.getReturnValue();
                    BDD updatedBdd = updatedReturn.getInputConstraints().and(currBdd);
                    BoolExpr updatedSmt = 
                        _context.mkAnd(updatedReturn.getInputSmtConstraints(), currSmt);
                    TransferBDDSMTResult updatedResult = 
                        res.setReturnValueBDDSMT(updatedBdd, updatedSmt);
                    // if we're on a path where e evaluates to false, then this path is done;
                    // otherwise we will evaluate the next conjunct in the next iteration
                    if (!updatedResult.getReturnValue().getAccepted()) {
                      finalResults.add(updatedResult);
                    } else {
                      nextResults.add(updatedResult);
                    }
                }
            );
          }
          currResults = nextResults;
        // BooleanExpr e is not supported; ignore it but record the fact that we encountered it
        } catch (UnsupportedOperationException ufe) {
          currResults.forEach(tr -> unsupported(ufe, tr.getReturnValue().getOutputRoute()));
        }
      }
      finalResults.addAll(currResults);

    } else if (expr instanceof MatchPrefixSet) {
      p.debug("MatchPrefixSet");
      MatchPrefixSet m = (MatchPrefixSet) expr;

      // MatchPrefixSet::evaluate obtains the prefix to match (either the destination network or
      // next-hop IP) from the original route, so we do the same here
      BDDSMT prefixSet = matchPrefixSet(p.indent(), _conf, m, _originalRoute);
      TransferBDDSMTResult bddsmtResult = result.setReturnValueBDDSMT(prefixSet);
      finalResults.add(bddsmtResult.setReturnValueAccepted(true));

    } else if (expr instanceof LegacyMatchAsPath) {
      p.debug("MatchAsPath");
      checkForAsPathMatchAfterUpdate(p);
      LegacyMatchAsPath legacyMatchAsPathNode = (LegacyMatchAsPath) expr;
      BDDSMT asPathPredicate =
          matchAsPathSetExpr(
              p.indent(), _conf, legacyMatchAsPathNode.getExpr(), routeForMatching(p));
      TransferBDDSMTResult bddsmtResult = result.setReturnValueBDDSMT(asPathPredicate);
      finalResults.add(bddsmtResult.setReturnValueAccepted(true));

    } else {
      throw new UnsupportedOperationException(expr.toString());
    }

    // in most cases above we have only provided the path corresponding to the predicate being true
    // so lastly, we add the path corresponding to the predicate being false

    // first get a predicate representing routes that don't go down any existing path that we've
    // created so far
    // synthesis unmatched bdd logical expression
    BDD matchedBdd = _factory.orAll(
        finalResults.stream()
            .map(r -> r.getReturnValue().getInputConstraints())
            .collect(Collectors.toList())
    );
    BDD unmatchedBdd = matchedBdd.not();

    // synthesis unmatched smt logical expression
    BoolExpr matchedSmt = _context.mkOr(
        finalResults.stream()
            .map(r -> r.getReturnValue().getInputSmtConstraints())
            .toArray(BoolExpr[]::new)
    );
    // String unmatchedExprName = smtExprName(UNMATCHED, ++_exprIndex);
    String unmatchedExprName = smtExprName(UNMATCHED);
    BoolExpr unmatchedSmt = _context.mkBoolConst(unmatchedExprName);
    unmatchedSmt = _context.mkNot(matchedSmt);

    // if unmatched, then add a non-accepting path corresponding to that predicate
    if (!unmatchedBdd.isZero()) {
      TransferBDDSMTResult remaining = 
          new TransferBDDSMTResult(new BDDSMTRoute(result.getReturnValue().getOutputRoute()));
      TransferBDDSMTResult bddsmtRemaining = 
          remaining.setReturnValueBDDSMT(unmatchedBdd, unmatchedSmt);
      finalResults.add(bddsmtRemaining.setReturnValueAccepted(false));
    }

    // return match bdd and smt logical expression finalResults
    return ImmutableList.copyOf(finalResults);
  }

  /*
   * Symbolic analysis of a single route-policy statement.
   * Produces one TransferResult per path through the given statement.
   */
  private List<TransferBDDSMTState> compute(Statement stmt, TransferBDDSMTState state)
      throws UnsupportedOperationException {
    TransferBDDSMTParam curP = state.getTransferParam();
    TransferBDDSMTResult result = state.getTransferResult();

    if (stmt instanceof StaticStatement) {
      StaticStatement ss = (StaticStatement) stmt;

      switch (ss.getType()) {
        case ExitAccept:
          curP.debug("ExitAccept");
          result = exitValue(result, true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case ReturnTrue:
          curP.debug("ReturnTrue");
          result = returnValue(result, true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case ExitReject:
          curP.debug("ExitReject");
          result = exitValue(result, false);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case ReturnFalse:
          curP.debug("ReturnFalse");
          result = returnValue(result, false);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case SetDefaultActionAccept:
          curP.debug("SetDefaultActionAccept");
          curP = curP.setDefaultAccept(true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case SetDefaultActionReject:
          curP.debug("SetDefaultActionReject");
          curP = curP.setDefaultAccept(false);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case SetLocalDefaultActionAccept:
          curP.debug("SetLocalDefaultActionAccept");
          curP = curP.setDefaultAcceptLocal(true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case SetLocalDefaultActionReject:
          curP.debug("SetLocalDefaultActionReject");
          curP = curP.setDefaultAcceptLocal(false);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case ReturnLocalDefaultAction:
          curP.debug("ReturnLocalDefaultAction");
          result = returnValue(result, curP.getDefaultAcceptLocal());
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case DefaultAction:
          curP.debug("DefaultAction");
          result = exitValue(result, curP.getDefaultAccept());
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case FallThrough:
          curP.debug("Fallthrough");
          result = fallthrough(result);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case Return:
          curP.debug("Return");
          result = result.setReturnAssignedValue(true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case Suppress:
          curP.debug("Suppress");
          result = suppressedValue(result, true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case Unsuppress:
          curP.debug("Unsuppress");
          result = suppressedValue(result, false);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        /*
         * These directives are used by the Batfish route simulation to control the handling of
         * route updates that implicitly involve both a "read" and a "write". For example, Batfish
         * models an additive community set of 40:40 as a write of (InputCommunities U 40:40). For
         * some config formats InputCommunities should refer to the communities of the original
         * route, but for others it should refer to the current community set that reflects prior
         * updates. To account for the latter semantics, Batfish inserts directives to read from
         * and write to the intermediate attributes.
         *
         * <p>This code, {@link TransferBDD}, properly handles two common cases: 1) platforms that
         * never use these directives, so that the original route attributes are always read; and
         * 2) platforms that use the SetRead... and SetWrite... directives in such a way as to
         * ensure that they always read from the current set of route attributes, which reflect
         * all updates made so far by the route map. In principle these directives can allow for a
         * wider range of semantics to be expressed. For example, it is possible for writing to
         * intermediate attributes to be turned off at some point, so that later writes are no
         * longer recorded there (and hence are not seen by later reads). We can handle such
         * situations by introducing an explicit {@link BDDRoute} to represent the intermediate
         * BGP attributes.
         */
        case SetReadIntermediateBgpAttributes:
          curP = curP.setReadIntermediateBgpAttributes(true);
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        case SetWriteIntermediateBgpAttributes:
          return ImmutableList.of(toTransferBDDSMTState(curP, result));

        default:
          throw new UnsupportedOperationException(ss.getType().toString());
      }

    } else if (stmt instanceof If) {
      curP.debug("If");
      If i = (If) stmt;
      List<TransferBDDSMTResult> guardResults =
          compute(i.getGuard(), new TransferBDDSMTState(curP.indent(), result));

      // for each path coming from the guard, symbolically execute the appropriate branch of the If
      List<TransferBDDSMTState> newStates = new ArrayList<>();
      BDD currPathConditionBdd = result.getReturnValue().getInputConstraints();
      BoolExpr currPathConditionSmt = result.getReturnValue().getInputSmtConstraints();

      for (TransferBDDSMTResult guardResult : guardResults) {
        BDD pathConditionBdd =
            currPathConditionBdd.and(guardResult.getReturnValue().getInputConstraints());
        BoolExpr pathConditionSmt = _context.mkAnd(
            currPathConditionSmt, guardResult.getReturnValue().getInputSmtConstraints());

        // prune infeasible paths
        if (pathConditionBdd.isZero()) {
          continue;
        }

        BDDSMTRoute current = guardResult.getReturnValue().getOutputRoute();
        boolean accepted = guardResult.getReturnValue().getAccepted();

        TransferBDDSMTParam pCopy = curP.indent().setData(current);
        List<Statement> branch = accepted ? i.getTrueStatements() : i.getFalseStatements();
        newStates.addAll(compute(branch, ImmutableList.of(
            new TransferBDDSMTState(pCopy, result.setReturnValue(
                new TransferBDDSMTReturn(
                    current, pathConditionBdd, pathConditionSmt, 
                    result.getReturnValue().getAccepted()
                )
            ))
        )));
      }

      return ImmutableList.copyOf(newStates);

    } else if (stmt instanceof SetLocalPreference) {
      curP.debug("SetLocalPreference");
      SetLocalPreference slp = (SetLocalPreference) stmt;
      LongExpr ie = slp.getLocalPreference();
      MutableBDDSMTInteger newValue =
          applyLongExprModification(curP.indent(), curP.getData().getLocalPref(), ie);
      curP.getData().setLocalPref(newValue);
      return ImmutableList.of(toTransferBDDSMTState(curP, result));

    } else if (stmt instanceof SetCommunities) {
      curP.debug("SetCommunities");
      SetCommunities sc = (SetCommunities) stmt;
      CommunitySetExpr setExpr = sc.getCommunitySetExpr();
      // SetCommunitiesVisitor requires a BDDRoute that maps each community atomic predicate BDD
      // to its corresponding BDD variable, so we use the original route here
      CommunityAPDispositions dispositions =
          setExpr.accept(new SetCommunitiesVisitor(), new Arg(this, _originalRoute));
      updateCommunities(dispositions, curP);
      return ImmutableList.of(toTransferBDDSMTState(curP, result));

    } else if (stmt instanceof TraceableStatement) {
      return compute(((TraceableStatement) stmt).getInnerStatements(), ImmutableList.of(state));

    } else {
      throw new UnsupportedOperationException(stmt.toString());
    }
  }

  /*
   * Apply the effect of modifying a long value (e.g., to set the metric).
   * Overflows for IncrementMetric are handled by clipping to the max value.
   */
  private MutableBDDSMTInteger applyLongExprModification(
      TransferBDDSMTParam p, MutableBDDSMTInteger x, LongExpr e) 
      throws UnsupportedOperationException {
    if (e instanceof LiteralLong) {
      LiteralLong z = (LiteralLong) e;
      p.debug("LiteralLong: %s", z.getValue());
      return MutableBDDSMTInteger.makeFromValue(x.getFactory(), x.getContext(), 32, z.getValue());
    } else if (e instanceof IncrementMetric) {
      IncrementMetric z = (IncrementMetric) e;
      p.debug("Increment: %s", z.getAddend());
      return x.addClipping(
          MutableBDDSMTInteger.makeFromValue(x.getFactory(), x.getContext(), 32, z.getAddend()));
    } else {
      throw new UnsupportedOperationException(e.toString());
    }

    /* TODO: These old cases are not correct; removing for now since they are not currently used.
    First, they should dec/inc the corresponding field of the route, not whatever MutableBDDInteger x
    is passed in.  Second, they need to prevent overflow.  See LongExpr::evaluate for details.

    if (e instanceof DecrementMetric) {
      DecrementMetric z = (DecrementMetric) e;
      p.debug("Decrement: %s", z.getSubtrahend());
      return x.sub(MutableBDDInteger.makeFromValue(x.getFactory(), 32, z.getSubtrahend()));
    }
    if (e instanceof IncrementLocalPreference) {
      IncrementLocalPreference z = (IncrementLocalPreference) e;
      p.debug("IncrementLocalPreference: %s", z.getAddend());
      return x.add(MutableBDDInteger.makeFromValue(x.getFactory(), 32, z.getAddend()));
    }
    if (e instanceof DecrementLocalPreference) {
      DecrementLocalPreference z = (DecrementLocalPreference) e;
      p.debug("DecrementLocalPreference: %s", z.getSubtrahend());
      return x.sub(MutableBDDInteger.makeFromValue(x.getFactory(), 32, z.getSubtrahend()));
    }
     */
  }

  /**
   * Produces a BDD that represents the disjunction of all atomic predicates associated with any of
   * the given AS-path regexes.
   *
   * @param asPathRegexes the set of AS-path regexes to convert to a BDD
   * @param apMap a map from as-path regexes to their corresponding sets of atomic predicates
   * @param route the symbolic representation of a route
   * @return the BDD
   */
  public /*static*/ BDDSMT asPathRegexesToBDDSMT(
      Set<SymbolicAsPathRegex> asPathRegexes, Map<SymbolicAsPathRegex, Set<Integer>> apMap,
      BDDSMTRoute route) {
    Set<Integer> asPathAPs = atomicPredicatesFor(asPathRegexes, apMap);

    // synthesis a bdd expression that represents the disjunction of all as-path regexes APs
    BDD matchAspathBdd = 
        route.getFactory().orAll(asPathAPs.stream()
            .map(ap -> route.getAsPathRegexAtomicPredicates().value(ap))
            .collect(Collectors.toList()));

    // synthesis a smt expression that represents the disjunction of all as-path regexes APs
    // String aspathExprName = smtExprName(MATCH_ASPATH_REGEXES, ++_exprIndex);
    String aspathExprName = smtExprName(MATCH_ASPATH_REGEXES);
    BoolExpr matchAspathSmt = route.getContext().mkOr(
        asPathAPs.stream()
            .map(ap -> route.getAsPathRegexAtomicPredicates().valueSmt(ap, aspathExprName))
            .toArray(BoolExpr[]::new)
    );

    return new BDDSMT(matchAspathBdd, matchAspathSmt);
  }

  /**
   * Produces a set consisting of all atomic predicates associated with any of the given symbolic
   * regexes.
   *
   * @param regexes the regexes of interest
   * @param apMap a map from regexes to their corresponding sets of atomic predicates
   * @param <T> the specific type of the regexes
   * @return the set of relevant atomic predicates
   */
  static <T extends SymbolicRegex> Set<Integer> atomicPredicatesFor(
      Set<T> regexes, Map<T, Set<Integer>> apMap) {
    return regexes.stream()
        .flatMap(r -> apMap.get(r).stream())
        .collect(ImmutableSet.toImmutableSet());
  }


  // Create a TransferBDDState, using the BDDRoute in the given TransferResult and throwing away the
  // one that is in the given TransferParam.
  private TransferBDDSMTState toTransferBDDSMTState(
      TransferBDDSMTParam curP, TransferBDDSMTResult result) {
    return new TransferBDDSMTState(curP.setData(result.getReturnValue().getOutputRoute()), result);
  }

  // Produce a BDD representing conditions under which the route's destination prefix is within a
  // given prefix range.
  public /*static*/ BDDSMT isRelevantForDestination(BDDSMTRoute record, PrefixRange range) {
    SubRange r = range.getLengthRange();
    int lower = r.getStart();
    int upper = r.getEnd();

    // synthesis match prefix ip/length bdd logical expression
    BDD matchPrefixIpBdd = record.getPrefix().toBDD(range.getPrefix());
    BDD matchPrefixLengthBdd = record.getPrefixLength().range(lower, upper);
    BDD matchPrefixBdd = matchPrefixIpBdd.and(matchPrefixLengthBdd);

    // synthesis match prefix ip/length smt logical expression
    String matchPrefixIpExprName = smtExprName(MATCH_PREFIX_IP);
    String matchPrefixLengthExprName = smtExprName(MATCH_PREFIX_LENGTH);
    BoolExpr matchPrefixIpSmt = record.getPrefix().toSMT(range.getPrefix(), matchPrefixIpExprName);
    BoolExpr matchPrefixLengthSmt = 
        record.getPrefixLength().rangeSmt(lower, upper, matchPrefixLengthExprName);
    BoolExpr matchPrefixSmt = record.getContext().mkAnd(matchPrefixIpSmt, matchPrefixLengthSmt);

    return new BDDSMT(matchPrefixBdd, matchPrefixSmt);
  }

  // Produce a BDD representing conditions under which the route's next-hop address is within a
  // given prefix range.
  private /*static*/ BDDSMT isRelevantForNextHop(BDDSMTRoute record, PrefixRange range) {
    SubRange r = range.getLengthRange();
    int lower = r.getStart();
    int upper = r.getEnd();

    // the next hop has a prefix length of MAX_PREFIX_LENGTH (32); check that it is in range
    boolean lenMatch = lower <= Prefix.MAX_PREFIX_LENGTH && Prefix.MAX_PREFIX_LENGTH <= upper;
    if (lenMatch) {
      // synthesis match nexthop ip bdd logical expression
      BDD matchNexthopBdd = record.getNextHop().toBDD(range.getPrefix());
      // synthesis match nexthop ip smt logical expression
      String matchNexthopExprName = smtExprName(MATCH_NEXTHOP_IP);
      BoolExpr matchNexthopSmt = record.getNextHop().toSMT(range.getPrefix(), matchNexthopExprName);
      return new BDDSMT(matchNexthopBdd, matchNexthopSmt);
    } else {
      return new BDDSMT(record.getFactory().zero(), record.getContext().mkFalse());
    }
  }

  // Produce a BDD that is the symbolic representation of the given AsPathSetExpr predicate.
  private BDDSMT matchAsPathSetExpr(
      TransferBDDSMTParam p, Configuration conf, AsPathSetExpr e, BDDSMTRoute other)
      throws UnsupportedOperationException {
    if (e instanceof NamedAsPathSet) {
      NamedAsPathSet namedAsPathSet = (NamedAsPathSet) e;
      AsPathAccessList accessList = conf.getAsPathAccessLists().get(namedAsPathSet.getName());
      p.debug("Named As Path Set: %s", namedAsPathSet.getName());
      return matchAsPathAccessList(accessList, other);
    }
    // TODO: handle other kinds of AsPathSetExprs
    throw new UnsupportedOperationException(e.toString());
  }

  // Raise an exception if we are about to match on an as-path that has been previously updated
  // along this path; the analysis currently does not handle that situation.
  private void checkForAsPathMatchAfterUpdate(TransferBDDSMTParam p)
      throws UnsupportedOperationException {
    if ((_useOutputAttributes || p.getReadIntermediateBgpAtttributes())
        && !p.getData().getPrependedASes().isEmpty()) {
      throw new UnsupportedOperationException(
          "Matching on a modified as-path is not currently supported");
    }
  }

  /* Convert an AS-path access list to a boolean formula represented as a BDD. */
  private BDDSMT matchAsPathAccessList(AsPathAccessList accessList, BDDSMTRoute other) {
    List<AsPathAccessListLine> lines = new ArrayList<>(accessList.getLines());
    Collections.reverse(lines);

    // initialize bdd and smt logical expression
    BDD matchAspathAclBdd = _factory.zero();
    // create a named boolean smt variable and then initialize it with false
    // String aspathAclExprName = smtExprName(MATCH_ASPATH_ACCESSLIST, ++_exprIndex);
    String aspathAclExprName = smtExprName(MATCH_ASPATH_ACCESSLIST);
    BoolExpr matchAspathAclSmt = _context.mkBoolConst(aspathAclExprName);
    matchAspathAclSmt = _context.mkFalse();

    for (AsPathAccessListLine line : lines) {
      boolean action = (line.getAction() == LineAction.PERMIT);

      // each line's regex is represented as the disjunction of all of the regex's
      // corresponding atomic predicates
      SymbolicAsPathRegex regex = new SymbolicAsPathRegex(line.getRegex());
      BDDSMT regexApsBddsmt =
          asPathRegexesToBDDSMT(ImmutableSet.of(regex), _asPathRegexAtomicPredicates, other);
      BDD regexApsBdd = regexApsBddsmt.getBddVariable();
      BoolExpr regexApsSmt = regexApsBddsmt.getSmtVariable();

      // synthesis match aspath access list bdd logical expression
      matchAspathAclBdd = ite(regexApsBdd, mkBDD(action), matchAspathAclBdd);
      // synthesis match aspath access list smt logical expression
      // String actionPermitExprName = smtExprName(ACTION_PERMIT, ++_exprIndex);
      String actionPermitExprName = smtExprName(ACTION_PERMIT);
      BoolExpr actionSmt = _context.mkBoolConst(actionPermitExprName);
      actionSmt = action ? _context.mkTrue() : _context.mkFalse();
      matchAspathAclSmt = (BoolExpr) _context.mkITE(regexApsSmt, actionSmt, matchAspathAclSmt);
    }

    return new BDDSMT(matchAspathAclBdd, matchAspathAclSmt);
  }

  /*
   * Converts a route filter list to a boolean expression.
   */
  private BDDSMT matchFilterList(
      TransferBDDSMTParam p, RouteFilterList x, BDDSMTRoute other, 
      BiFunction<BDDSMTRoute, PrefixRange, BDDSMT> symbolicMatcher)
      throws UnsupportedOperationException {
    List<RouteFilterLine> lines = new ArrayList<>(x.getLines());
    Collections.reverse(lines);

    // initialize bdd and smt logical expression
    BDD matchFilterListBdd = _factory.zero();
    // create a named boolean smt variable and then initialize it with false
    // String filterListExprName = smtExprName(MATCH_FILTER_LIST, ++_exprIndex);
    String filterListExprName = smtExprName(MATCH_FILTER_LIST);
    BoolExpr matchFilterListSmt = _context.mkBoolConst(filterListExprName);
    matchFilterListSmt = _context.mkFalse();

    for (RouteFilterLine line : lines) {
      if (!line.getIpWildcard().isPrefix()) {
        throw new UnsupportedOperationException(line.getIpWildcard().toString());
      }

      boolean action = (line.getAction() == LineAction.PERMIT);

      Prefix pfx = line.getIpWildcard().toPrefix();
      SubRange r = line.getLengthRange();
      PrefixRange range = new PrefixRange(pfx, r);
      p.debug("Prefix Range: %s", range);
      p.debug("Action: %s", line.getAction());

      BDDSMT matchesBddsmt = symbolicMatcher.apply(other, range);
      BDD matchesBdd = matchesBddsmt.getBddVariable();
      BoolExpr matchesSmt = matchesBddsmt.getSmtVariable();

      // synthesis match filter list bdd logical expression
      matchFilterListBdd = ite(matchesBdd, mkBDD(action), matchFilterListBdd);
      // synthesis match filter list smt logical expression
      // String actionPermitExprName = smtExprName(ACTION_PERMIT, ++_exprIndex);
      String actionPermitExprName = smtExprName(ACTION_PERMIT);
      BoolExpr actionSmt = _context.mkBoolConst(actionPermitExprName);
      matchFilterListSmt = (BoolExpr) _context.mkITE(matchesSmt, actionSmt, matchFilterListSmt);
    }

    return new BDDSMT(matchFilterListBdd, matchFilterListSmt);
  }

  // Returns a function that can convert a prefix range into a BDD that constrains the appropriate
  // part of a route (destination prefix or next-hop IP), depending on the given prefix
  // expression.
  private BiFunction<BDDSMTRoute, PrefixRange, BDDSMT> prefixExprToSymbolicMatcher(PrefixExpr pe)
      throws UnsupportedOperationException {
    if (pe.equals(DestinationNetwork.instance())) {
      // return TransferBDDSMT::isRelevantForDestination;
      return this::isRelevantForDestination;

    } else if (pe instanceof IpPrefix) {
      IpPrefix ipp = (IpPrefix) pe;
      if (ipp.getIp().equals(NextHopIp.instance())
          && ipp.getPrefixLength().equals(new LiteralInt(Prefix.MAX_PREFIX_LENGTH))) {
        // return TransferBDDSMT::isRelevantForNextHop;
        return this::isRelevantForNextHop;
      }
    }

    throw new UnsupportedOperationException(pe.toString());
  }

  /*
   * Converts a prefix set to a boolean expression.
   */
  private BDDSMT matchPrefixSet(
      TransferBDDSMTParam p, Configuration conf, MatchPrefixSet m, BDDSMTRoute other)
      throws UnsupportedOperationException {
    BiFunction<BDDSMTRoute, PrefixRange, BDDSMT> symbolicMatcher =
        prefixExprToSymbolicMatcher(m.getPrefix());
    PrefixSetExpr e = m.getPrefixSet();

    if (e instanceof ExplicitPrefixSet) {
      ExplicitPrefixSet x = (ExplicitPrefixSet) e;

      Set<PrefixRange> ranges = x.getPrefixSpace().getPrefixRanges();
      BDD matchPrefixSetBdd = _factory.zero();
      // String prefixSetExprName = smtExprName(MATCH_PREFIX_SET, ++_exprIndex);
      String prefixSetExprName = smtExprName(MATCH_PREFIX_SET);
      BoolExpr matchPrefixSetSmt = _context.mkBoolConst(prefixSetExprName);
      matchPrefixSetSmt = _context.mkFalse();

      for (PrefixRange range : ranges) {
        p.debug("Prefix Range: %s", range);
        // synthesis bdd and smt logical expression
        BDDSMT bddsmt = symbolicMatcher.apply(other, range);
        matchPrefixSetBdd = matchPrefixSetBdd.or(bddsmt.getBddVariable());
        matchPrefixSetSmt = _context.mkOr(matchPrefixSetSmt, bddsmt.getSmtVariable());
      }

      return new BDDSMT(matchPrefixSetBdd, matchPrefixSetSmt);

    } else if (e instanceof NamedPrefixSet) {
      NamedPrefixSet x = (NamedPrefixSet) e;

      String name = x.getName();
      RouteFilterList fl = conf.getRouteFilterLists().get(name);
      p.debug("Named: %s", name);

      // synthesis bdd and smt logical expression
      return matchFilterList(p, fl, other, symbolicMatcher);

    } else {
      throw new UnsupportedOperationException(e.toString());
    }
  }

  // NOTE: commented by yongzheng in 20250120
  // // Produce a BDD representing a constraint on the given MutableBDDInteger that enforces the
  // // integer equality constraint represented by the given IntComparator and long value
  // private BDD matchLongValueComparison(IntComparator comp, long val, MutableBDDInteger bddInt)
  //     throws UnsupportedOperationException {
  //   switch (comp) {
  //     case EQ:
  //       return bddInt.value(val);
  //     case GE:
  //       return bddInt.geq(val);
  //     case GT:
  //       return bddInt.geq(val).and(bddInt.value(val).not());
  //     case LE:
  //       return bddInt.leq(val);
  //     case LT:
  //       return bddInt.leq(val).and(bddInt.value(val).not());
  //     default:
  //       throw new IllegalArgumentException(
  //           "Unexpected int comparison " + comp.getClass().getSimpleName());
  //   }
  // }

  // NOTE: commented by yongzheng in 20250120
  // // Produce a BDD representing a constraint on the given MutableBDDInteger that enforces the
  // // integer equality constraint represented by the given IntComparator and IntExpr
  // private BDD matchIntComparison(IntComparator comp, IntExpr expr, MutableBDDInteger bddInt)
  //     throws UnsupportedOperationException {
  //   if (!(expr instanceof LiteralInt)) {
  //     throw new UnsupportedOperationException(expr.toString());
  //   }
  //   int val = ((LiteralInt) expr).getValue();
  //   return matchLongValueComparison(comp, val, bddInt);
  // }

  // NOTE: commented by yongzheng in 20250120
  // // Produce a BDD representing a constraint on the given MutableBDDInteger that enforces the
  // // integer (in)equality constraint represented by the given IntComparator and LongExpr
  // private BDD matchLongComparison(IntComparator comp, LongExpr expr, MutableBDDInteger bddInt)
  //     throws UnsupportedOperationException {
  //   if (!(expr instanceof LiteralLong)) {
  //     throw new UnsupportedOperationException(expr.toString());
  //   }
  //   long val = ((LiteralLong) expr).getValue();
  //   return matchLongValueComparison(comp, val, bddInt);
  // }

  // NOTE: commented by yongzheng in 20250120
  // private void setNextHop(NextHopExpr expr, BDDRoute route) throws UnsupportedOperationException {
  //   // record the fact that the next-hop has been explicitly set by the route-map
  //   route.setNextHopSet(true);
  //   if (expr instanceof DiscardNextHop) {
  //     route.setNextHopType(BDDRoute.NextHopType.DISCARDED);
  //   } else if (expr instanceof IpNextHop && ((IpNextHop) expr).getIps().size() == 1) {
  //     route.setNextHopType(BDDRoute.NextHopType.IP);
  //     List<Ip> ips = ((IpNextHop) expr).getIps();
  //     Ip ip = ips.get(0);
  //     route.setNextHop(MutableBDDInteger.makeFromValue(_factory, 32, ip.asLong()));
  //   } else if (expr instanceof BgpPeerAddressNextHop) {
  //     route.setNextHopType(BDDRoute.NextHopType.BGP_PEER_ADDRESS);
  //   } else if (expr instanceof SelfNextHop) {
  //     route.setNextHopType(BDDRoute.NextHopType.SELF);
  //   } else {
  //     throw new UnsupportedOperationException(expr.toString());
  //   }
  // }

  // NOTE: commented by yongzheng in 20250120
  // private void prependASPath(AsPathListExpr expr, BDDRoute route)
  //     throws UnsupportedOperationException {
  //   // currently we only support prepending AS literals
  //   if (!(expr instanceof LiteralAsList)) {
  //     throw new UnsupportedOperationException(expr.toString());
  //   }
  //   List<Long> prependedASes = new ArrayList<>();
  //   LiteralAsList asList = (LiteralAsList) expr;
  //   for (AsExpr ase : asList.getList()) {
  //     if (!(ase instanceof ExplicitAs)) {
  //       throw new UnsupportedOperationException(ase.toString());
  //     }
  //     prependedASes.add(((ExplicitAs) ase).getAs());
  //   }
  //   prependedASes.addAll(route.getPrependedASes());
  //   route.setPrependedASes(prependedASes);
  // }

  // TODO added by yongzheng to (maybe) modify this method in 20250120
  // Update community atomic predicates based on the given CommunityAPDispositions object
  private void updateCommunities(CommunityAPDispositions dispositions, TransferBDDSMTParam curP) {
    BDD[] commAPBDDs = curP.getData().getCommunityAtomicPredicates();
    BDD[] currAPBDDs = routeForMatching(curP).getCommunityAtomicPredicates();
    for (int i = 0; i < currAPBDDs.length; i++) {
      if (dispositions.getMustExist().contains(i)) {
        commAPBDDs[i] = mkBDD(true);
      } else if (dispositions.getMustNotExist().contains(i)) {
        commAPBDDs[i] = mkBDD(false);
      } else {
        commAPBDDs[i] = currAPBDDs[i];
      }
    }
  }

  /**
   * A BDD representing the conditions under which the current statement is not reachable, because
   * we've already returned or exited before getting there.
   *
   * @param currState the current state of the analysis
   * @return the bdd
   */
  private static boolean unreachable(TransferBDDSMTResult currState) {
    return currState.getReturnAssignedValue() || currState.getExitAssignedValue();
  }

  // If the analysis encounters a routing policy feature that is not currently supported, we ignore
  // it and keep going, but we also log a warning and mark the output BDDRoute as having reached an
  // unsupported feature.
  private void unsupported(UnsupportedOperationException e, BDDSMTRoute route) {
    Level level = _unsupportedAlreadyWarned.add(e.getMessage()) ? Level.WARN : Level.DEBUG;
    LOGGER.log(level, "Unsupported statement in routing policy {} of node {}: {}", 
        _policy.getName(), _conf.getHostname(), e.getMessage());
    route.setUnsupported(true);
  }

  /*
   * Create the result of reaching a suppress or unsuppress statement.
   */
  private TransferBDDSMTResult suppressedValue(TransferBDDSMTResult r, boolean val) {
    return r.setSuppressedValue(val);
  }

  /*
   * Create the result of reaching a return statement, returning with the given value.
   */
  private TransferBDDSMTResult returnValue(TransferBDDSMTResult r, boolean accepted) {
    return r.setReturnValue(r.getReturnValue().setAccepted(accepted))
        .setReturnAssignedValue(true)
        .setFallthroughValue(false);
  }

  /*
   * Create the result of reaching an exit statement, returning with the given value.
   */
  private TransferBDDSMTResult exitValue(TransferBDDSMTResult r, boolean accepted) {
    return r.setReturnValue(r.getReturnValue().setAccepted(accepted))
        .setExitAssignedValue(true)
        .setFallthroughValue(false);
  }

  private TransferBDDSMTResult fallthrough(TransferBDDSMTResult r) {
    return r.setFallthroughValue(true).setReturnAssignedValue(true);
  }

  // Returns the appropriate route to use for matching on attributes.
  private BDDSMTRoute routeForMatching(TransferBDDSMTParam p) {
    return _useOutputAttributes || p.getReadIntermediateBgpAtttributes()
        ? p.getData()
        : _originalRoute;
  }

  /** Return a smt expression name accoring to exprName. */
  // private static String smtExprName(String exprName, long exprIndex) {
  //   return exprName + exprIndex;
  // }
  private /*static*/ String smtExprName(String exprName) {
      ++_exprIndex;
      return exprName + _exprIndex;
  }

  /** Return a BDD from a boolean. */
  public BDD mkBDD(boolean b) {
    return b ? _factory.one() : _factory.zero();
  }

  /** If-then-else statement. */
  public BDD ite(BDD b, BDD x, BDD y) {
    return b.ite(x, y);
  }

  /** Find the BDD corresponding to an item that is being tracked symbolically. */
  private BDD itemToBDD(String item, List<String> items, BDD[] itemsBDDs) {
    int index = items.indexOf(item);
    return itemsBDDs[index];
  }

  public Map<CommunityVar, Set<Integer>> getCommunityAtomicPredicates() {
    return _communityAtomicPredicates;
  }

  public Configuration getConfiguration() {
    return _conf;
  }

  public BDDFactory getFactory() {
    return _factory;
  }

  public Context getContext() {
    return _context;
  }

  public ConfigAtomicPredicates getConfigAtomicPredicates() {
    return _configAtomicPredicates;
  }

  public BDDSMTRoute getOriginalRoute() {
    return _originalRoute;
  }

  public boolean getUseOutputAttributes() {
    return _useOutputAttributes;
  }

  public RoutingPolicy getPolicy() {
    return _policy;
  }
}
