package org.batfish.datamodel.routing_policy.expr;

import static com.google.common.base.MoreObjects.firstNonNull;
import static com.google.common.base.MoreObjects.toStringHelper;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedSet;
import java.util.Collection;
import java.util.Set;
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

  private final Set<Community> _communities;

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
  private boolean _enableSmtVariable;
  private String _configVarPrefix;

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
  public void initSmtVariable(Context context, Solver solver, String configVarPrefix, boolean isTrue) {
    // assert that the literal community set is not shared
    if (_enableSmtVariable) {
      System.out.println("ERROR LiteralCommunitySet:initSmtVariable");
      System.out.println("Previous configVarPrefix: " + _configVarPrefix);
      System.out.println("Current  configVarPrefix: " + configVarPrefix);
      return;
    }

    for (Community community : _communities) {
      // check and avoid shared object
      if (community.getEnableSmtVariable()) {
        if (community instanceof ExtendedCommunity) {
          ExtendedCommunity extendedCommunity = (ExtendedCommunity) community;
          community =
              ExtendedCommunity.of(
                  extendedCommunity.getSubType(),
                  extendedCommunity.getGlobalAdministrator(),
                  extendedCommunity.getLocalAdministrator());
        } else if (community instanceof StandardCommunity) {
          StandardCommunity standardCommunity = (StandardCommunity) community;
          community = StandardCommunity.of(standardCommunity.asLong());
        } else if (community instanceof LargeCommunity) {
          LargeCommunity largeCommunity = (LargeCommunity) community;
            community =
                LargeCommunity.of(
                    largeCommunity.getGlobalAdministrator(),
                    largeCommunity.getLocalData1(),
                    largeCommunity.getLocalData2());
        } else {
          throw new BatfishException(
              "Unimplemented community type: " + community.getClass().getName());
        }
      }

      // init smt variable for community
      String communityString = format(community.getCommunityString());
      configVarPrefix += communityString + "_";
      community.initSmtVariable(context, solver, configVarPrefix, isTrue);
    }

    // configure enable smt variable flag to true
    _enableSmtVariable = isTrue;
    _configVarPrefix = configVarPrefix;
  }

  @Override
  public void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    initSmtVariable(context, solver, configVarPrefix, true);
  }

  @Override
  public boolean getEnableSmtVariable() {
    return _enableSmtVariable;
  }

  public String getConfigVarPrefix() {
    return _configVarPrefix;
  }

  /** Add get community expression string for configVarPrefix */
  @Override
  public String getCommunityExprString() {
    // TODO: implement me when needed
    return "";
  }
}
