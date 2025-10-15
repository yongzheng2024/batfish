package org.batfish.datamodel.routing_policy.expr;

import static com.google.common.base.MoreObjects.firstNonNull;
import static com.google.common.base.MoreObjects.toStringHelper;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedSet;
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;
import java.util.SortedSet;
import javax.annotation.Nonnull;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.bgp.community.Community;
import org.batfish.datamodel.bgp.community.ExtendedCommunity;
import org.batfish.datamodel.bgp.community.StandardCommunity;
import org.batfish.datamodel.bgp.community.LargeCommunity;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.visitors.CommunitySetExprVisitor;
import org.batfish.datamodel.visitors.VoidCommunitySetExprVisitor;

/**
 * A {@link CommunitySetExpr} matching community-sets containing ANY of the communities returned by
 * {@link #getCommunities()}.
 */
public class LiteralCommunitySet extends CommunitySetExpr {
  private static final String PROP_COMMUNITIES = "communities";

  @JsonCreator
  private static @Nonnull LiteralCommunitySet create(
      @JsonProperty(PROP_COMMUNITIES) Set<Community> communities) {
    return new LiteralCommunitySet(firstNonNull(communities, ImmutableSet.of()));
  }

  private /*final*/ Set<Community> _communities;

  public LiteralCommunitySet(@Nonnull Collection<? extends Community> communities) {
    _communities = ImmutableSet.copyOf(communities);

    // initialize enable smt variable flag to false
    _enableSmtVariable = false;
  }

  @Override
  public <T> T accept(CommunitySetExprVisitor<T> visitor) {
    return visitor.visitLiteralCommunitySet(this);
  }

  @Override
  public void accept(VoidCommunitySetExprVisitor visitor) {
    visitor.visitLiteralCommunitySet(this);
  }

  /**
   * When treated as a literal set of communities, represents exactly the set returned by {@link
   * #getCommunities()}.
   */
  @Nonnull
  @Override
  public Set<Community> asLiteralCommunities(@Nonnull Environment environment) {
    return _communities;
  }

  @Override
  public boolean dynamicMatchCommunity() {
    return false;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof LiteralCommunitySet)) {
      return false;
    }
    return _communities.equals(((LiteralCommunitySet) obj)._communities);
  }

  public @Nonnull Set<Community> getCommunities() {
    return _communities;
  }

  @Override
  public int hashCode() {
    return _communities.hashCode();
  }

  @Override
  public boolean matchCommunities(Environment environment, Set<Community> communitySetCandidate) {
    return communitySetCandidate.stream().anyMatch(_communities::contains);
  }

  @Override
  public boolean matchCommunity(Environment environment, Community community) {
    return _communities.contains(community);
  }

  @Override
  public boolean reducible() {
    return true;
  }

  @Override
  public String toString() {
    return toStringHelper(getClass()).add(PROP_COMMUNITIES, _communities).toString();
  }

  @JsonProperty(PROP_COMMUNITIES)
  private @Nonnull SortedSet<Community> getJsonCommunities() {
    return ImmutableSortedSet.copyOf(_communities);
  }

  /** Add configuration constant - SMT symbolic variable */
  // private boolean _enableSmtVariable;
  // private String _configVarPrefix;

  private static String format(String str) {
    String formatedStr = "";
    for (char c : str.toCharArray()) {
      switch (c) {
        case ':':
          formatedStr += "_";
          break;
        default:
          formatedStr += c;
          break;
      }
    }
    return formatedStr;
  }

  @Override
  public void initSmtVariable(
      Context context, Solver solver, String configVarPrefix, boolean isTrue) {
    // assert that the literal community set is not shared
    if (_enableSmtVariable) {
      throw new BatfishException("LiteralCommunitySet.initSmtVariable: shared object.\n" +
          "Previous configVarPrefix: " + _configVarPrefix + "\n" +
          "Current  configVarPrefix: " + configVarPrefix);
    }

    // backup and clear communities set
    Set<Community> communitiesBackup = new HashSet<>(_communities);
    Set<Community> communities = new HashSet<>();

    // check and avoid shared object
    for (Community community : communitiesBackup) {
      if (community.getEnableSmtVariable()) {
        System.out.println("WARNING: LiteralCommunitySet:initSmtVariable: " +
            "found shared Community, cloning it.");

        Community communityBackup = community;
        // clone community shared object
        community = cloneCommunity(community);

        // add additional assert for using shared object
        if (communityBackup.getEnableSmtVariable() == community.getEnableSmtVariable()) {
          throw new BatfishException("LiteralCommunitySet:initSmtVariable: " +
              "cloning failed for shared object.");
        }
      }

      // add relevant community to communities set
      communities.add(community);
    }

    // copy back communities set
    _communities = ImmutableSet.copyOf(communities);

    // init smt variable for community
    for (Community community : _communities) {
      String communityString = format(community.getCommunityString());
      String configVarPrefixUpdated = configVarPrefix + communityString + "_";
      community.initSmtVariable(context, solver, configVarPrefixUpdated, isTrue);
    }

    // configure enable smt variable flag to true
    _enableSmtVariable = true;
    _configVarPrefix = configVarPrefix;
  }

  @Override
  public void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    initSmtVariable(context, solver, configVarPrefix, true);
  }

  /** Add get community expression string for configVarPrefix */
  @Override
  public String getCommunityExprString() {
    // TODO: implement me when needed
    throw new BatfishException("LiteralCommunitySet:getCommunityExprString: not implemented yet.");
  }
}
