package org.batfish.datamodel;

import static com.google.common.base.MoreObjects.toStringHelper;
import static java.util.Objects.requireNonNull;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import java.io.Serializable;
import java.util.Objects;
import javax.annotation.Nonnull;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.datamodel.routing_policy.expr.CommunitySetExpr;
import org.batfish.datamodel.routing_policy.expr.LiteralCommunity;
import org.batfish.datamodel.routing_policy.expr.LiteralCommunitySet;

/** A line in a CommunityList */
public class CommunityListLine implements Serializable {
  private static final String PROP_ACTION = "action";
  private static final String PROP_MATCH_CONDITION = "matchCondition";

  public static @Nonnull CommunityListLine accepting(CommunitySetExpr matchCondition) {
    return new CommunityListLine(LineAction.PERMIT, matchCondition);
  }

  private final LineAction _action;

  private final CommunitySetExpr _matchCondition;

  public CommunityListLine(@Nonnull LineAction action, @Nonnull CommunitySetExpr matchCondition) {
    _action = action;
    _matchCondition = matchCondition;

    // initialize enable smt variable flag to false
    _enableSmtVariable = false;
  }

  @JsonCreator
  private static @Nonnull CommunityListLine create(
      @JsonProperty(PROP_ACTION) LineAction action,
      @JsonProperty(PROP_MATCH_CONDITION) CommunitySetExpr matchCondition) {
    return new CommunityListLine(requireNonNull(action), requireNonNull(matchCondition));
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (!(o instanceof CommunityListLine)) {
      return false;
    }
    CommunityListLine other = (CommunityListLine) o;
    return _action == other._action && _matchCondition.equals(other._matchCondition);
  }

  /** The action the underlying access-list will take when this line matches a route. */
  @JsonProperty(PROP_ACTION)
  public @Nonnull LineAction getAction() {
    return _action;
  }

  @JsonProperty(PROP_MATCH_CONDITION)
  public @Nonnull CommunitySetExpr getMatchCondition() {
    return _matchCondition;
  }

  @Override
  public int hashCode() {
    return Objects.hash(_action.ordinal(), _matchCondition);
  }

  @Override
  public String toString() {
    return toStringHelper(getClass())
        .add(PROP_ACTION, _action)
        .add(PROP_MATCH_CONDITION, _matchCondition)
        .toString();
  }

  /** Add configuration constant - SMT symbolic variable */
  private boolean _enableSmtVariable;
  private String _configVarPrefix;

  private transient BoolExpr _configVarAction;

  public void initSmtVariable(
      Context context, Solver solver, String configVarPrefix, boolean isTrue) {
    if (_enableSmtVariable) {
      System.out.println("ERROR CommunityListLine:initSmtVariable");
      System.out.println("Previous configVarPrefix: " + _configVarPrefix);
      System.out.println("Current  configVarPrefix: " + configVarPrefix);
      return;
    }

    // if (_matchCondition instanceof RegexCommunitySet) {
    //   RegexCommunitySet rcs = (RegexCommunitySet) _matchCondition;
    //   String regexCommunity = rcs.getRegex();
    //   configVarPrefix = configVarPrefix + "_" + regexCommunity + "__";
    // } else if (_matchCondition instanceof LiteralCommunity) {
    //   LiteralCommunity lc = (LiteralCommunity) _matchCondition;
    //   String community = lc.getCommunity().toString();
    //   configVarPrefix = configVarPrefix + "_" + community + "__";
    // } else {
    //   throw new IllegalArgumentException("Unimplemented community condition: " + _matchCondition);
    // }

    _configVarAction = context.mkBoolConst(configVarPrefix + "action");

    // add relevant configuration constant constraint
    BoolExpr configVarActionConstraint = context.mkEq(
        _configVarAction, context.mkBool(_action == LineAction.PERMIT));
    solver.add(configVarActionConstraint);

    _matchCondition.initSmtVariable(context, solver, configVarPrefix, isTrue);

    // configure enable smt variable flag to true
    _enableSmtVariable = true;
    _configVarPrefix = configVarPrefix;
  }

  public void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    initSmtVariable(context, solver, configVarPrefix, true);
  }

  public boolean getEnableSmtVariable() {
    return _enableSmtVariable;
  }

  public String getConfigVarPrefix() {
    return _configVarPrefix;
  }

  public BoolExpr getConfigVarAction() {
    return _configVarAction;
  }
}