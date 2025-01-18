package org.batfish.minesweeper.bddsmt;

import static org.batfish.minesweeper.bddsmt.BDDSMTDomain.numBits;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.math.IntMath;
import com.google.common.math.LongMath;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import javax.annotation.Nonnull;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.AbstractRoute;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.OriginType;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.bgp.TunnelEncapsulationAttribute;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.IDeepCopy;
import org.batfish.minesweeper.OspfType;

// import org.batfish.minesweeper.bddsmt.BDDSMTDomain;
import org.batfish.common.bddsmt.MutableBDDSMTInteger;
import org.batfish.minesweeper.bdd.BDDTunnelEncapsulationAttribute;

import com.microsoft.z3.Context;

/**
 * A collection of attributes describing a route advertisement, used for symbolic route analysis.
 *
 * @author Ryan Beckett
 */
public final class BDDSMTRoute implements IDeepCopy<BDDSMTRoute> {

  /*
   * For each bit i of a route announcement we have both a BDD variable vi, which
   * represents the ith bit of the announcement, and a BDD fi (f stands for formula), representing
   * the conditions under which bit i is set to 1. Initially each fi is simply vi. The {@link
   * TransferBDD} class takes a BDDRoute and a route policy and produces a new BDDRoute whose fi
   * BDDs represent all possible output announcements from that route policy and the conditions
   * under which they occur, in terms of the vi variables (which still represent the bits of the
   * original input announcement).
   * 
   * TODO not understand the above comment by yongzheng in 20250107
   *
   * Since most fields of the route announcement are integers, for example local preference,
   * there is a {@link BDDInteger} helper class that uses this encoding to represent a
   * symbolic integer, along with integer-specific operations.
   */

  private static List<OspfType> allMetricTypes;

  static {
    allMetricTypes = new ArrayList<>();
    allMetricTypes.add(OspfType.O);
    allMetricTypes.add(OspfType.OIA);
    allMetricTypes.add(OspfType.E1);
    allMetricTypes.add(OspfType.E2);
  }

  private final BDDFactory _factory;

  private final Context _context;

  private MutableBDDSMTInteger _adminDist;

  private Map<Integer, String> _bitNames;

  /**
   * Each community atomic predicate (see class Graph) is allocated both a BDD variable and a BDD,
   * as in the general encoding described above. This array maintains the BDDs. The nth BDD
   * indicates the conditions under which a community matching the nth atomic predicate exists in
   * the route.
   */
  private BDD[] _communityAtomicPredicates;

  /**
   * Unlike the case for communities, where each route contains a set of communities, exactly one
   * AS-path atomic predicate will be true for any concrete route. Therefore, we use a {@link
   * BDDSMTDomain}, which encodes the mutual exclusion constraint implicitly and also uses only a
   * logarithmic number of BDD variables in the number of atomic predicates.
   */
  private BDDSMTDomain<Integer> _asPathRegexAtomicPredicates;

  // for now we only track the cluster list's length, not its contents;
  // that is all that is needed to support matching on the length
  private MutableBDDSMTInteger _clusterListLength;

  private MutableBDDSMTInteger _localPref;

  private MutableBDDSMTInteger _med;

  // we use a BDDInteger to track the constraints on the next-hop IP, but we also track a few
  // additional pieces of information that are needed to properly account for the next-hop:  a
  // "type" that accounts for actions such as when a route map discards the next-hop, and a flag
  // indicating whether the route map explicitly updated the next hop

  // private MutableBDDSMTInteger _nextHop;
  private MutableBDDSMTInteger _nextHop;

  public enum NextHopType {
    BGP_PEER_ADDRESS,
    DISCARDED,
    IP,
    SELF
  }

  private NextHopType _nextHopType;

  // was the next-hop explicitly set?
  private boolean _nextHopSet;

  // egp, igp, or incomplete
  private BDDSMTDomain<OriginType> _originType;

  // intra area (O), inter area (OIA), external type 1 (E1), or external type 2 (E2)
  private BDDSMTDomain<OspfType> _ospfMetric;

  // private final MutableBDDSMTInteger _prefix;
  private final MutableBDDSMTInteger _prefix;

  // private final MutableBDDSMTInteger _prefixLength;
  private final MutableBDDSMTInteger _prefixLength;

  /**
   * A sequence of AS numbers that is prepended to the original AS-path. The use of a fully concrete
   * value here is sufficient to accurately represent the effects of a single execution path through
   * a route map, since any single path encounters a fixed set of AS-path prepend statements. Hence
   * this representation is sufficient to support {@link TransferBDD#computePaths()}, which produces
   * one BDDRoute per execution path. However, this representation precludes the use of a BDDRoute
   * to accurately represent the effects of multiple execution paths, unless those paths prepend the
   * same exact sequence of ASes to the AS-path.
   */
  private @Nonnull List<Long> _prependedASes;

  private final BDDSMTDomain<RoutingProtocol> _protocolHistory;

  /**
   * Represents the route's optional next-hop interface name. See {@link
   * org.batfish.datamodel.routing_policy.expr.MatchInterface}.
   */
  private final BDDSMTDomain<Integer> _nextHopInterfaces;

  /**
   * Represents the optional source VRF from which the route was sent. See {@link
   * org.batfish.datamodel.routing_policy.expr.MatchSourceVrf}.
   */
  private final BDDSMTDomain<Integer> _sourceVrfs;

  /**
   * Represents the optional {@link org.batfish.datamodel.bgp.TunnelEncapsulationAttribute} on the
   * route.
   */
  private @Nonnull BDDTunnelEncapsulationAttribute _tunnelEncapsulationAttribute;

  private MutableBDDSMTInteger _tag;

  /**
   * Contains a BDD variable for each "track" that may be encountered along the path. See {@link
   * org.batfish.datamodel.routing_policy.expr.TrackSucceeded}.
   */
  private BDD[] _tracks;

  private MutableBDDSMTInteger _weight;

  // whether the analysis encountered an unsupported route-policy
  // statement/expression
  private boolean _unsupported;

  /**
   * The routing protocols allowed in a BGP route announcement (see {@link
   * org.batfish.datamodel.BgpRoute}).
   */
  public static final Set<RoutingProtocol> ALL_BGP_PROTOCOLS =
      ImmutableSet.of(RoutingProtocol.AGGREGATE, RoutingProtocol.BGP, RoutingProtocol.IBGP);

  /**
   * A constructor that obtains the number of atomic predicates for community and AS-path regexes
   * from a given {@link ConfigAtomicPredicates} object.
   */
  public BDDSMTRoute(BDDFactory factory, Context context, ConfigAtomicPredicates aps) {
    this(
        factory,
        context,
        aps.getStandardCommunityAtomicPredicates().getNumAtomicPredicates()
            + aps.getNonStandardCommunityLiterals().size(),
        aps.getAsPathRegexAtomicPredicates().getNumAtomicPredicates(),
        aps.getNextHopInterfaces().size(),
        aps.getSourceVrfs().size(),
        aps.getTracks().size(),
        aps.getTunnelEncapsulationAttributes());
  }

  /**
   * Creates a collection of BDD variables representing the various attributes of a control plane
   * advertisement. Each atomic predicate created to represent community regexes will be allocated a
   * BDD variable and a BDD, and similarly for the atomic predicates for AS-path regexes, so the
   * number of such atomic predicates is provided.
   */
  @VisibleForTesting
  BDDSMTRoute(
      BDDFactory factory,
      Context context,
      int numCommAtomicPredicates,
      int numAsPathRegexAtomicPredicates,
      int numNextHopInterfaces,
      int numSourceVrfs,
      int numTracks,
      List<TunnelEncapsulationAttribute> tunnelEncapsulationAttributes) {
    _factory = factory;
    _context = context;

    int bitsToRepresentAdmin = IntMath.log2(AbstractRoute.MAX_ADMIN_DISTANCE, RoundingMode.CEILING);
    // or else we need to do tricks in the BDDInteger.
    assert LongMath.isPowerOfTwo(1L + AbstractRoute.MAX_ADMIN_DISTANCE);
    int numVars = factory.varNum();
    int numNeeded =
        32 * 6
            + 16
            + bitsToRepresentAdmin
            + 6
            + numCommAtomicPredicates
            + numBits(numAsPathRegexAtomicPredicates)
            // we track one extra value for the next-hop interfaces and source VRFs, to represent
            // "none", since these are optional parts of a route
            + numBits(numNextHopInterfaces + 1)
            + numBits(numSourceVrfs + 1)
            + numTracks
            + BDDTunnelEncapsulationAttribute.numBitsFor(tunnelEncapsulationAttributes)
            + numBits(OriginType.values().length)
            + numBits(RoutingProtocol.values().length)
            + numBits(allMetricTypes.size());
    if (numVars < numNeeded) {
      factory.setVarNum(numNeeded);
    }
    _bitNames = new HashMap<>();

    int idx = 0;
    // Initialize one BDD per community atomic predicate, each of which has a corresponding
    // BDD variable
    _communityAtomicPredicates = new BDD[numCommAtomicPredicates];
    for (int i = 0; i < numCommAtomicPredicates; i++) {
      _communityAtomicPredicates[i] = factory.ithVar(idx);
      _bitNames.put(idx, "community atomic predicate " + i);
      idx++;
    }
    _protocolHistory =
        new BDDSMTDomain<>(factory, context, ImmutableList.copyOf(RoutingProtocol.values()), idx);
    int len = _protocolHistory.getInteger().size();
    addBitNames("proto", len, idx, false);
    idx += len;
    _originType = new BDDSMTDomain<>(factory, context, ImmutableList.copyOf(OriginType.values()), idx);
    len = _originType.getInteger().size();
    addBitNames("origin", len, idx, false);
    idx += len;
    // Initialize integer values
    _med = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, false);
    addBitNames("med", 32, idx, false);
    idx += 32;
    _nextHop = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, false);
    addBitNames("nextHop", 32, idx, false);
    idx += 32;
    _nextHopSet = false;
    _nextHopType = NextHopType.IP;
    _tag = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, false);
    addBitNames("tag", 32, idx, false);
    idx += 32;
    _weight = MutableBDDSMTInteger.makeFromIndex(factory, context, 16, idx, false);
    addBitNames("weight", 16, idx, false);
    idx += 16;
    _adminDist = MutableBDDSMTInteger.makeFromIndex(factory, context, bitsToRepresentAdmin, idx, false);
    addBitNames("ad", bitsToRepresentAdmin, idx, false);
    idx += bitsToRepresentAdmin;
    _localPref = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, false);
    addBitNames("lp", 32, idx, false);
    idx += 32;
    _clusterListLength = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, false);
    addBitNames("clusterListLength", 32, idx, false);
    idx += 32;
    // need 6 bits for prefix length because there are 33 possible values, 0 - 32
    _prefixLength = MutableBDDSMTInteger.makeFromIndex(factory, context, 6, idx, true);
    addBitNames("pfxLen", 6, idx, true);
    idx += 6;
    _prefix = MutableBDDSMTInteger.makeFromIndex(factory, context, 32, idx, true);
    addBitNames("pfx", 32, idx, true);
    idx += 32;

    _asPathRegexAtomicPredicates =
        new BDDSMTDomain<>(
            factory, context, 
            IntStream.range(0, numAsPathRegexAtomicPredicates).boxed().collect(Collectors.toList()),
            idx);
    len = _asPathRegexAtomicPredicates.getInteger().size();
    addBitNames("as-path atomic predicates", len, idx, false);
    idx += len;

    // we track one extra value for the next-hop interfaces and source VRFs, to represent
    // "none", since these are optional parts of a route
    _nextHopInterfaces =
        new BDDSMTDomain<>(
            factory, context, 
            IntStream.range(0, numNextHopInterfaces + 1).boxed().collect(Collectors.toList()),
            idx);
    len = _nextHopInterfaces.getInteger().size();
    addBitNames("next-hop interfaces", len, idx, false);
    idx += len;
    _sourceVrfs =
        new BDDSMTDomain<>(
            factory, context, 
            IntStream.range(0, numSourceVrfs + 1).boxed().collect(Collectors.toList()),
            idx);
    len = _sourceVrfs.getInteger().size();
    addBitNames("source VRFs", len, idx, false);
    idx += len;

    // Initialize one BDD per tracked name, each of which has a corresponding BDD variable
    _tracks = new BDD[numTracks];
    for (int i = 0; i < numTracks; i++) {
      _tracks[i] = factory.ithVar(idx);
      _bitNames.put(idx, "track " + i);
      idx++;
    }

    // Tunnel encapsulation attribute is an optional singleton
    _tunnelEncapsulationAttribute =
        BDDTunnelEncapsulationAttribute.create(factory, idx, tunnelEncapsulationAttributes);
    len = _tunnelEncapsulationAttribute.getNumBits();
    addBitNames("tunnel encapsulation attributes", len, idx, false);
    idx += len;

    // Initialize OSPF type
    _ospfMetric = new BDDSMTDomain<>(factory, context, allMetricTypes, idx);
    len = _ospfMetric.getInteger().size();
    addBitNames("ospfMetric", len, idx, false);
    idx += len;

    _prependedASes = new ArrayList<>();

    // Initially there are no unsupported statements encountered
    _unsupported = false;

    assert idx != 0; // unnecessary, but needed to avoid unused comment
  }

  /*
   * Create a BDDRecord from another. Because BDDs are immutable,
   * there is no need for a deep copy.
   */
  public BDDSMTRoute(BDDSMTRoute other) {
    _factory = other._factory;
    _context = other._context;

    _asPathRegexAtomicPredicates = new BDDSMTDomain<>(other._asPathRegexAtomicPredicates);
    _clusterListLength = new MutableBDDSMTInteger(other._clusterListLength);
    _communityAtomicPredicates = other._communityAtomicPredicates.clone();
    _prefixLength = new MutableBDDSMTInteger(other._prefixLength);
    _prefix = new MutableBDDSMTInteger(other._prefix);
    _nextHop = new MutableBDDSMTInteger(other._nextHop);
    _nextHopSet = other._nextHopSet;
    _nextHopType = other._nextHopType;
    _adminDist = new MutableBDDSMTInteger(other._adminDist);
    _med = new MutableBDDSMTInteger(other._med);
    _tag = new MutableBDDSMTInteger(other._tag);
    _weight = new MutableBDDSMTInteger(other._weight);
    _localPref = new MutableBDDSMTInteger(other._localPref);
    _protocolHistory = new BDDSMTDomain<>(other._protocolHistory);
    _originType = new BDDSMTDomain<>(other._originType);
    _ospfMetric = new BDDSMTDomain<>(other._ospfMetric);
    _bitNames = other._bitNames;
    _prependedASes = new ArrayList<>(other._prependedASes);
    _nextHopInterfaces = new BDDSMTDomain<>(other._nextHopInterfaces);
    _sourceVrfs = new BDDSMTDomain<>(other._sourceVrfs);
    _tracks = other._tracks.clone();
    _tunnelEncapsulationAttribute =
        BDDTunnelEncapsulationAttribute.copyOf(other._tunnelEncapsulationAttribute);
    _unsupported = other._unsupported;
  }

  /*
   * Constructs a new BDDRoute by restricting the given one to conform to the predicate pred.
   *
   * @param pred the predicate used to restrict the output routes
   * @param route a symbolic route represented as a transformation on a set of routes (input).
   */
  public BDDSMTRoute(BDD pred, BDDSMTRoute route) {
    _factory = route._factory;
    _context = route._context;

    // Create a fresh array for community atomic predicates
    BDD[] communityAtomicPredicates = new BDD[route._communityAtomicPredicates.length];
    // Intersect each atomic predicate with pred.
    for (int i = 0; i < communityAtomicPredicates.length; i++) {
      communityAtomicPredicates[i] = route._communityAtomicPredicates[i].and(pred);
    }

    _asPathRegexAtomicPredicates = new BDDSMTDomain<>(pred, route._asPathRegexAtomicPredicates);
    _clusterListLength = route.getClusterListLength().and(pred);
    _communityAtomicPredicates = communityAtomicPredicates;
    _prefixLength = route.getPrefixLength().and(pred);
    _prefix = route.getPrefix().and(pred);
    _nextHop = route.getNextHop().and(pred);
    _adminDist = route.getAdminDist().and(pred);
    _med = route.getMed().and(pred);
    _tag = route.getTag().and(pred);
    _localPref = route.getLocalPref().and(pred);
    _weight = route.getWeight().and(pred);
    _protocolHistory = new BDDSMTDomain<>(pred, route.getProtocolHistory());
    _originType = new BDDSMTDomain<>(pred, route.getOriginType());
    _ospfMetric = new BDDSMTDomain<>(pred, route.getOspfMetric());
    _bitNames = route._bitNames;
    _nextHopSet = route.getNextHopSet();
    _nextHopType = route.getNextHopType();
    _unsupported = route.getUnsupported();
    _prependedASes = new ArrayList<>(route.getPrependedASes());
    _nextHopInterfaces = new BDDSMTDomain<>(pred, route._nextHopInterfaces);
    _sourceVrfs = new BDDSMTDomain<>(pred, route._sourceVrfs);
    _tracks = route.getTracks();
    _tunnelEncapsulationAttribute = route._tunnelEncapsulationAttribute.and(pred);
  }

  /*
   * Helper function that builds a map from BDD variable index
   * to some more meaningful name. Helpful for debugging.
   */
  private void addBitNames(String s, int length, int index, boolean reverse) {
    for (int i = index; i < index + length; i++) {
      if (reverse) {
        _bitNames.put(i, s + (length - 1 - (i - index)));
      } else {
        _bitNames.put(i, s + (i - index + 1));
      }
    }
  }

  /*
   * Convenience method for the copy constructor
   */
  @Override
  public BDDSMTRoute deepCopy() {
    return new BDDSMTRoute(this);
  }

  /**
   * Create a BDD representing the constraint that the value of a specific enum attribute in the
   * route announcement's protocol is a member of the given set.
   *
   * @param elements the set of elements that are allowed
   * @param bddDomain the attribute to be constrained
   * @return the BDD representing this constraint
   */
  public <T> BDD anyElementOf(Set<T> elements, BDDSMTDomain<T> bddDomain) {
    return _factory.orAll(elements.stream().map(bddDomain::value).collect(Collectors.toList()));
  }

  /**
   * Not all assignments to the BDD variables that make up a BDDRoute represent valid BGP routes.
   * This method produces constraints that well-formed BGP routes must satisfy, represented as a
   * BDD. It is useful when the goal is to produce concrete example BGP routes from a BDDRoute, for
   * instance.
   *
   * <p>Note that it does not suffice to enforce these constraints as part of symbolic route
   * analysis (see {@link TransferBDD}). That analysis computes a BDD representing the input routes
   * that are accepted by a given route map. Conjoining the well-formedness constraints with that
   * BDD would ensure that all models are feasible routes. But if a client of the analysis is
   * instead interested in routes that are denied by the route map, then negating that BDD and
   * obtaining models would be incorrect, because it would not ensure that the well-formedness
   * constraints hold.
   *
   * @return the constraints
   */
  public BDD bgpWellFormednessConstraints() {

    // the prefix length should be 32 or less
    BDD prefLenConstraint = _prefixLength.leq(32);
    // the next hop should be neither the min nor the max possible IP
    // this constraint is enforced by NextHopIp's constructor
    BDD nextHopConstraint = _nextHop.range(Ip.ZERO.asLong() + 1, Ip.MAX.asLong() - 1);
    // The various BDD Domains should all lie in the domain (needed if the domain is not power-of-2
    // in size).
    BDD asPathRegexValid = _asPathRegexAtomicPredicates.getIsValidConstraint();
    BDD nextHopInterfacesValid = _nextHopInterfaces.getIsValidConstraint();
    BDD originTypeValid = _originType.getIsValidConstraint();
    BDD ospfMetricValid = _ospfMetric.getIsValidConstraint();
    // Protocol domain constraint is stronger: only one of the ones allowed in a BgpRoute.
    BDD protocolConstraint = anyElementOf(ALL_BGP_PROTOCOLS, this.getProtocolHistory());
    BDD sourceVrfValid = _sourceVrfs.getIsValidConstraint();
    BDD tunnelEncapValid = _tunnelEncapsulationAttribute.getIsValidConstraint();
    return _factory.andAllAndFree(
        prefLenConstraint,
        nextHopConstraint,
        asPathRegexValid,
        nextHopInterfacesValid,
        originTypeValid,
        ospfMetricValid,
        protocolConstraint,
        sourceVrfValid,
        tunnelEncapValid);
  }

  /*
   * Converts a BDD to the graphviz DOT format for debugging.
   */
  String dot(BDD bdd) {
    StringBuilder sb = new StringBuilder();
    sb.append("digraph G {\n");
    sb.append("0 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];\n");
    sb.append("1 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];\n");
    dotRec(sb, bdd, new HashSet<>());
    sb.append("}");
    return sb.toString();
  }

  public String dotWrapper(BDD bdd) {
    return dot(bdd);
  }

  /*
   * Creates a unique id for a bdd node when generating
   * a DOT file for graphviz
   */
  private Integer dotId(BDD bdd) {
    if (bdd.isZero()) {
      return 0;
    }
    if (bdd.isOne()) {
      return 1;
    }
    return bdd.hashCode() + 2;
  }

  /*
   * Recursively builds each of the intermediate BDD nodes in the
   * graphviz DOT format.
   */
  private void dotRec(StringBuilder sb, BDD bdd, Set<BDD> visited) {
    if (bdd.isOne() || bdd.isZero() || visited.contains(bdd)) {
      return;
    }
    int val = dotId(bdd);
    int valLow = dotId(bdd.low());
    int valHigh = dotId(bdd.high());
    String name = _bitNames.get(bdd.var());
    sb.append(val).append(" [label=\"").append(name).append("\"]\n");
    sb.append(val).append(" -> ").append(valLow).append("[style=dotted]\n");
    sb.append(val).append(" -> ").append(valHigh).append("[style=filled]\n");
    visited.add(bdd);
    dotRec(sb, bdd.low(), visited);
    dotRec(sb, bdd.high(), visited);
  }

  public MutableBDDSMTInteger getAdminDist() {
    return _adminDist;
  }

  public void setAdminDist(MutableBDDSMTInteger adminDist) {
    _adminDist = adminDist;
  }

  public BDDSMTDomain<Integer> getAsPathRegexAtomicPredicates() {
    return _asPathRegexAtomicPredicates;
  }

  public void setAsPathRegexAtomicPredicates(BDDSMTDomain<Integer> asPathRegexAtomicPredicates) {
    _asPathRegexAtomicPredicates = asPathRegexAtomicPredicates;
  }

  public MutableBDDSMTInteger getClusterListLength() {
    return _clusterListLength;
  }

  public void setClusterListLength(MutableBDDSMTInteger clusterListLength) {
    _clusterListLength = clusterListLength;
  }

  public BDD[] getCommunityAtomicPredicates() {
    return _communityAtomicPredicates;
  }

  public void setCommunityAtomicPredicates(BDD[] communityAtomicPredicates) {
    _communityAtomicPredicates = communityAtomicPredicates;
  }

  public BDDFactory getFactory() {
    return _factory;
  }

  public Context getContext() {
    return _context;
  }

  public MutableBDDSMTInteger getLocalPref() {
    return _localPref;
  }

  public void setLocalPref(MutableBDDSMTInteger localPref) {
    _localPref = localPref;
  }

  public MutableBDDSMTInteger getMed() {
    return _med;
  }

  public void setMed(MutableBDDSMTInteger med) {
    _med = med;
  }

  public MutableBDDSMTInteger getNextHop() {
    return _nextHop;
  }

  public void setNextHop(MutableBDDSMTInteger nextHop) {
    _nextHop = nextHop;
  }

  public boolean getNextHopSet() {
    return _nextHopSet;
  }

  public void setNextHopSet(boolean nextHopSet) {
    _nextHopSet = nextHopSet;
  }

  public NextHopType getNextHopType() {
    return _nextHopType;
  }

  public void setNextHopType(NextHopType nextHopType) {
    _nextHopType = nextHopType;
  }

  public BDDSMTDomain<OriginType> getOriginType() {
    return _originType;
  }

  public void setOriginType(BDDSMTDomain<OriginType> originType) {
    _originType = originType;
  }

  public BDDSMTDomain<OspfType> getOspfMetric() {
    return _ospfMetric;
  }

  public void setOspfMetric(BDDSMTDomain<OspfType> ospfMetric) {
    _ospfMetric = ospfMetric;
  }

  public MutableBDDSMTInteger getPrefix() {
    return _prefix;
  }

  public MutableBDDSMTInteger getPrefixLength() {
    return _prefixLength;
  }

  public List<Long> getPrependedASes() {
    return _prependedASes;
  }

  public void setPrependedASes(List<Long> prependedASes) {
    _prependedASes = prependedASes;
  }

  public BDDSMTDomain<RoutingProtocol> getProtocolHistory() {
    return _protocolHistory;
  }

  public MutableBDDSMTInteger getTag() {
    return _tag;
  }

  public void setTag(MutableBDDSMTInteger tag) {
    _tag = tag;
  }

  public void setTunnelEncapsulationAttribute(@Nonnull BDDTunnelEncapsulationAttribute value) {
    _tunnelEncapsulationAttribute = value;
  }

  public BDDSMTDomain<Integer> getNextHopInterfaces() {
    return _nextHopInterfaces;
  }

  public BDDSMTDomain<Integer> getSourceVrfs() {
    return _sourceVrfs;
  }

  public BDD[] getTracks() {
    return _tracks;
  }

  public void setTracks(BDD[] tracks) {
    _tracks = tracks;
  }

  public @Nonnull BDDTunnelEncapsulationAttribute getTunnelEncapsulationAttribute() {
    return _tunnelEncapsulationAttribute;
  }

  public MutableBDDSMTInteger getWeight() {
    return _weight;
  }

  public void setWeight(MutableBDDSMTInteger weight) {
    _weight = weight;
  }

  public boolean getUnsupported() {
    return _unsupported;
  }

  public void setUnsupported(boolean unsupported) {
    _unsupported = unsupported;
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (o == null || !(o instanceof BDDSMTRoute)) {
      return false;
    }
    BDDSMTRoute other = (BDDSMTRoute) o;
    return Objects.equals(_adminDist, other._adminDist)
        && Objects.equals(_ospfMetric, other._ospfMetric)
        && Objects.equals(_originType, other._originType)
        && Objects.equals(_protocolHistory, other._protocolHistory)
        && Objects.equals(_med, other._med)
        && Objects.equals(_localPref, other._localPref)
        && Objects.equals(_clusterListLength, other._clusterListLength)
        && Objects.equals(_tag, other._tag)
        && Objects.equals(_weight, other._weight)
        && Objects.equals(_nextHop, other._nextHop)
        && Objects.equals(_nextHopSet, other._nextHopSet)
        && Objects.equals(_nextHopType, other._nextHopType)
        && Objects.equals(_prefix, other._prefix)
        && Objects.equals(_prefixLength, other._prefixLength)
        && Arrays.equals(_communityAtomicPredicates, other._communityAtomicPredicates)
        && Objects.equals(_asPathRegexAtomicPredicates, other._asPathRegexAtomicPredicates)
        && Objects.equals(_prependedASes, other._prependedASes)
        && Objects.equals(_nextHopInterfaces, other._nextHopInterfaces)
        && Objects.equals(_sourceVrfs, other._sourceVrfs)
        && Arrays.equals(_tracks, other._tracks)
        && _tunnelEncapsulationAttribute.equals(other._tunnelEncapsulationAttribute)
        && Objects.equals(_unsupported, other._unsupported);
  }

  @Override
  public int hashCode() {
    // does not include all fields, but that's okay as hash code doesn't need to be perfect.
    return Objects.hash(
        _adminDist,
        _originType,
        _med,
        _localPref,
        _clusterListLength,
        _tag,
        _weight,
        _nextHop,
        _prefix,
        _prefixLength,
        Arrays.hashCode(_communityAtomicPredicates),
        _asPathRegexAtomicPredicates,
        _prependedASes);
  }
}
