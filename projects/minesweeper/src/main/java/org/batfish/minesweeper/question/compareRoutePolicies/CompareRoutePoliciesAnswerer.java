package org.batfish.minesweeper.question.compareRoutePolicies;

import static org.batfish.minesweeper.bdd.BDDRouteDiff.computeDifferences;
import static org.batfish.minesweeper.bdd.ModelGeneration.constraintsToModel;
import static org.batfish.minesweeper.bdd.ModelGeneration.satAssignmentToInputRoute;
import static org.batfish.question.testroutepolicies.TestRoutePoliciesAnswerer.diffRowResultsFor;
import static org.batfish.specifier.NameRegexRoutingPolicySpecifier.ALL_ROUTING_POLICIES;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.JFactory;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.AbstractRoute;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.BDDRouteDiff;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.question.testroutepolicies.TestRoutePoliciesAnswerer;
import org.batfish.specifier.AllNodesNodeSpecifier;
import org.batfish.specifier.NodeSpecifier;
import org.batfish.specifier.RoutingPolicySpecifier;
import org.batfish.specifier.SpecifierContext;
import org.batfish.specifier.SpecifierFactories;

/** An answerer for {@link CompareRoutePoliciesQuestion}. */
@SuppressWarnings("DuplicatedCode")
@ParametersAreNonnullByDefault
public final class CompareRoutePoliciesAnswerer extends Answerer {

  @Nonnull private final Environment.Direction _direction;

  @Nonnull private final String _policySpecifierString;
  @Nonnull private final String _proposedPolicySpecifierString;
  @Nonnull private final RoutingPolicySpecifier _policySpecifier;
  @Nonnull private final RoutingPolicySpecifier _proposedPolicySpecifier;

  @Nonnull private final NodeSpecifier _nodeSpecifier;

  @Nonnull private final Set<String> _communityRegexes;
  @Nonnull private final Set<String> _asPathRegexes;

  public CompareRoutePoliciesAnswerer(CompareRoutePoliciesQuestion question, IBatfish batfish) {
    super(question, batfish);
    _nodeSpecifier =
        SpecifierFactories.getNodeSpecifierOrDefault(
            question.getNodes(), AllNodesNodeSpecifier.INSTANCE);
    _direction = question.getDirection();

    _policySpecifierString = question.getPolicy();
    _policySpecifier =
        SpecifierFactories.getRoutingPolicySpecifierOrDefault(
            _policySpecifierString, ALL_ROUTING_POLICIES);

    _proposedPolicySpecifierString = question.getProposedPolicy();
    _proposedPolicySpecifier =
        SpecifierFactories.getRoutingPolicySpecifierOrDefault(
            _proposedPolicySpecifierString, ALL_ROUTING_POLICIES);

    // in the future, it may improve performance to combine all input community regexes
    // into a single regex representing their disjunction, and similarly for all output
    // community regexes, in order to minimize the number of atomic predicates that are
    // created and tracked by the analysis
    _communityRegexes = ImmutableSet.<String>builder().build();
    _asPathRegexes = ImmutableSet.<String>builder().build();
  }

  /**
   * Convert the results of symbolic route analysis into an answer to this question, if the
   * resulting constraints are satisfiable.
   *
   * @param policy the first route policy that was analyzed
   * @param proposedPolicy the second route policy that was analyzed
   * @return the concrete input route and, if the desired action is PERMIT, the concrete output
   *     routes resulting from analyzing the given policies.
   */
  private Row computeDifferencesForInputRoute(
      RoutingPolicy policy, RoutingPolicy proposedPolicy, Bgpv4Route inRoute) {
    return diffRowResultsFor(policy, proposedPolicy, inRoute, _direction);
  }

  /**
   * @param constraints Logical constraints that describe a set of routes.
   * @param configAPs the atomic predicates used for communities/as-paths.
   * @return An input route that conforms to the given constraints.
   */
  private Bgpv4Route constraintsToInputs(BDD constraints, ConfigAtomicPredicates configAPs) {
    assert (!constraints.isZero());
    BDD fullModel = constraintsToModel(constraints, configAPs);
    return satAssignmentToInputRoute(fullModel, configAPs);
  }

  /**
   * @param tbdd the transfer function to symbolically evaluate
   * @return the set of paths generated by symbolic execution
   */
  private List<TransferReturn> computePaths(TransferBDD tbdd) {
    try {
      return tbdd.computePaths(ImmutableSet.of());
    } catch (Exception e) {
      throw new BatfishException(
          "Unexpected error analyzing policy "
              + tbdd.getPolicy().getName()
              + " in node "
              + tbdd.getPolicy().getOwner().getHostname(),
          e);
    }
  }

  /**
   * @param factory the BDD factory used for this analysis
   * @param diffs A list of differences found between two output routes.
   * @param r1 the first of the two output routes that were compared
   * @param r2 the second of the two output routes that were compared
   * @return A BDD that denotes at least one of the differences in the given diffs list. Only
   *     capturing differences in communities and as-path for now; the rest are not necessary
   *     because they do not have additive semantics, like "set community additive" and "set as-path
   *     prepend". (actually, I think you might be able to plus on the local-pref value, TODO:
   *     check)
   */
  private BDD counterExampleOutputConstraints(
      BDDFactory factory, List<BDDRouteDiff.DifferenceType> diffs, BDDRoute r1, BDDRoute r2) {
    BDD acc = factory.zero();
    for (BDDRouteDiff.DifferenceType d : diffs) {
      switch (d) {
        case OSPF_METRIC:
        case LOCAL_PREF:
        case MED:
        case NEXTHOP:
        case NEXTHOP_DISCARDED:
        case NEXTHOP_SET:
        case TAG:
        case ADMIN_DIST:
        case WEIGHT:
        case UNSUPPORTED:
          break;
        case COMMUNITIES:
          BDD[] communityAtomicPredicates = r1.getCommunityAtomicPredicates();
          BDD[] otherCommunityAtomicPredicates = r2.getCommunityAtomicPredicates();
          for (int i = 0; i < communityAtomicPredicates.length; i++) {
            BDD outConstraint = communityAtomicPredicates[i].xor(otherCommunityAtomicPredicates[i]);
            // If there is a scenario where the two outputs differ at this community then ensure
            // this scenario
            // manifests during model generation.
            acc = acc.or(outConstraint);
          }
        case AS_PATH:
          BDD[] asPathAtomicPredicates = r1.getAsPathRegexAtomicPredicates();
          BDD[] otherAsPathAtomicPredicates = r2.getAsPathRegexAtomicPredicates();
          for (int i = 0; i < asPathAtomicPredicates.length; i++) {
            BDD outConstraint = asPathAtomicPredicates[i].xor(otherAsPathAtomicPredicates[i]);
            // If there is a scenario where the two outputs differ at this community then ensure
            // this scenario
            // manifests during model generation.
            acc = acc.or(outConstraint);
          }
      }
    }
    if (!acc.isZero()) {
      // If we have accumulated some constraints from the output routes then return these
      return acc;
    } else {
      // otherwise return true.
      return factory.one();
    }
  }

  /**
   * Compare two route policies for behavioral differences.
   *
   * @param policy the routing policy
   * @param proposedPolicy the proposed routing policy
   * @param configAPs an object providing the atomic predicates for the policy's owner configuration
   * @return a set of differences
   */
  private List<Row> comparePolicies(
      RoutingPolicy policy, RoutingPolicy proposedPolicy, ConfigAtomicPredicates configAPs) {
    // The set of differences if any.
    List<BDD> differences = new ArrayList<>();

    BDDFactory factory = JFactory.init(100000, 10000);
    TransferBDD tBDD = new TransferBDD(factory, configAPs, policy);
    TransferBDD otherTBDD = new TransferBDD(factory, configAPs, proposedPolicy);

    // Generate well-formedness constraints
    BDD wf = new BDDRoute(tBDD.getFactory(), configAPs).bgpWellFormednessConstraints();

    // The set of paths for the current policy
    List<TransferReturn> paths = computePaths(tBDD);
    // The set of paths for the proposed policy
    List<TransferReturn> otherPaths = computePaths(otherTBDD);

    // Potential optimization: if a set of input routes between the two paths is the same then we
    // only need to validate
    // the outputs between this pair; the intersection with all others is going to be empty.
    // This will probably be more efficient when we expect the two route-maps to be (almost)
    // equivalent.
    for (TransferReturn path : paths) {
      for (TransferReturn otherPath : otherPaths) {
        BDD inputRoutes = path.getSecond();
        BDD inputRoutesOther = otherPath.getSecond();
        BDD intersection = inputRoutesOther.and(inputRoutes).and(wf);

        // If the sets of input routes between the two paths intersect, then these paths describe
        // some common
        // input routes and their behavior should match.
        if (!intersection.isZero()) {
          // Naive check to see if both policies accepted/rejected the route(s).
          if (path.getAccepted() != otherPath.getAccepted()) {
            differences.add(intersection);
          } else {
            // If both policies perform the same action, then check that their outputs match.
            // We compute the outputs of interest, by restricting the sets of output routes to the
            // intersection of the input routes and then comparing them.
            // We only need to compare the outputs if the routes were permitted.
            if (path.getAccepted()) {
              BDDRoute outputRoutes = new BDDRoute(intersection, path.getFirst());
              BDDRoute outputRoutesOther = new BDDRoute(intersection, otherPath.getFirst());
              List<BDDRouteDiff.DifferenceType> diff =
                  computeDifferences(outputRoutes, outputRoutesOther);
              // Compute any constraints on the output routes.
              BDD outputConstraints =
                  counterExampleOutputConstraints(factory, diff, outputRoutes, outputRoutesOther);
              if (!diff.isEmpty()) {
                differences.add(intersection.and(outputConstraints));
              }
            }
          }
        }
      }
    }
    return differences.stream()
        .map(intersection -> constraintsToInputs(intersection, configAPs))
        .sorted(Comparator.comparing(AbstractRoute::getNetwork))
        .map(r -> computeDifferencesForInputRoute(policy, proposedPolicy, r))
        .collect(Collectors.toList());
  }

  /**
   * Search all of the route policies of a particular node for behaviors of interest.
   *
   * @param node the node - for now assuming a single config, might lift that assumption later.
   * @param policies all route policies in that node
   * @param proposedPolicies all route policies in that node
   * @return all results from analyzing those route policies
   */
  private Stream<Row> comparePoliciesForNode(
      String node,
      Stream<RoutingPolicy> policies,
      Stream<RoutingPolicy> proposedPolicies,
      NetworkSnapshot snapshot) {
    List<RoutingPolicy> policiesList = policies.collect(Collectors.toList());
    List<RoutingPolicy> proposedPoliciesList = proposedPolicies.collect(Collectors.toList());

    if (policiesList.isEmpty()) {
      throw new IllegalArgumentException(
          String.format("Could not find policy matching %s", _policySpecifierString));
    }
    if (proposedPoliciesList.isEmpty()) {
      throw new IllegalArgumentException(
          String.format(
              "Could not find proposed policy matching %s", _proposedPolicySpecifierString));
    }

    // Compute AtomicPredicates for both policies and proposedPolicies.
    List<RoutingPolicy> allPolicies = new ArrayList<>(policiesList);
    allPolicies.addAll(proposedPoliciesList);

    ConfigAtomicPredicates configAPs =
        new ConfigAtomicPredicates(
            _batfish,
            snapshot,
            node,
            _communityRegexes.stream()
                .map(CommunityVar::from)
                .collect(ImmutableSet.toImmutableSet()),
            _asPathRegexes,
            allPolicies);

    return policiesList.stream()
        .flatMap(
            policy ->
                proposedPoliciesList.stream()
                    .flatMap(
                        proposedPolicy ->
                            comparePolicies(policy, proposedPolicy, configAPs).stream()));
  }

  @Override
  public AnswerElement answer(NetworkSnapshot snapshot) {
    SpecifierContext context = _batfish.specifierContext(snapshot);

    // Using stream.sorted() to ensure consistent order.
    List<Row> rows =
        _nodeSpecifier.resolve(context).stream()
            .sorted()
            .flatMap(
                node ->
                    comparePoliciesForNode(
                        node,
                        _policySpecifier.resolve(node, context).stream().sorted(),
                        _proposedPolicySpecifier.resolve(node, context).stream().sorted(),
                        snapshot))
            .collect(ImmutableList.toImmutableList());
    TableAnswerElement answerElement =
        new TableAnswerElement(TestRoutePoliciesAnswerer.compareMetadata());
    answerElement.postProcessAnswer(_question, rows);
    return answerElement;
  }

  @Nonnull
  @VisibleForTesting
  NodeSpecifier getNodeSpecifier() {
    return _nodeSpecifier;
  }

  @Nonnull
  @VisibleForTesting
  RoutingPolicySpecifier getPolicySpecifier() {
    return _policySpecifier;
  }

  @Nonnull
  @VisibleForTesting
  RoutingPolicySpecifier getProposedPolicySpecifier() {
    return _proposedPolicySpecifier;
  }
}