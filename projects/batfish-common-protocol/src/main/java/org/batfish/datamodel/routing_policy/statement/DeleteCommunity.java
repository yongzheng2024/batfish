package org.batfish.datamodel.routing_policy.statement;

import static com.google.common.base.Preconditions.checkArgument;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.BgpRoute;
import org.batfish.datamodel.bgp.community.Community;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.Result;
import org.batfish.datamodel.routing_policy.expr.CommunitySetExpr;

@ParametersAreNonnullByDefault
public final class DeleteCommunity extends Statement {
  private static final String PROP_EXPR = "expr";

  // @Nonnull private final CommunitySetExpr _expr;
  @Nonnull private CommunitySetExpr _expr;

  @JsonCreator
  private static DeleteCommunity jsonCreator(
      @Nullable @JsonProperty(PROP_EXPR) CommunitySetExpr expr) {
    checkArgument(expr != null, "%s must be provided", PROP_EXPR);
    return new DeleteCommunity(expr);
  }

  public DeleteCommunity(CommunitySetExpr expr) {
    _expr = expr;
  }

  @Override
  public <T, U> T accept(StatementVisitor<T, U> visitor, U arg) {
    return visitor.visitDeleteCommunity(this, arg);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    } else if (!(obj instanceof DeleteCommunity)) {
      return false;
    }
    DeleteCommunity other = (DeleteCommunity) obj;
    return _expr.equals(other._expr);
  }

  @Override
  public Result execute(Environment environment) {
    BgpRoute.Builder<?, ?> outputRouteBuilder =
        (BgpRoute.Builder<?, ?>) environment.getOutputRoute();
    Set<Community> currentCommunities = outputRouteBuilder.getCommunitiesAsSet();
    Set<Community> matchingCommunities = _expr.matchedCommunities(environment, currentCommunities);
    outputRouteBuilder.removeCommunities(matchingCommunities);
    Result result = new Result();
    return result;
  }

  @JsonProperty(PROP_EXPR)
  @Nonnull
  public CommunitySetExpr getExpr() {
    return _expr;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + _expr.hashCode();
    return result;
  }

  /** Add configuration constant - SMT symbolic variable */
  private boolean _enableSmtVariable;
  private String _configVarPrefix;

  public void initSmtVariable(
      Context context, Solver solver, String configVarPrefix, boolean isTrue) {
    // assert that the delete community is not shared
    if (_enableSmtVariable) {
      throw new BatfishException("DeleteCommunity.initSmtVariable: shared object.\n" +
              "Previous configVarPrefix: " + _configVarPrefix + "\n" +
              "Current  configVarPrefix: " + configVarPrefix);
    }

    // check and avoid shared object
    if (_expr.getEnableSmtVariable()) {
      System.out.println("WARNING: DeleteCommunity.initSmtVariable: " +
              "found shared Community Set Expr, cloning it.");

      CommunitySetExpr exprBackup = _expr;
      // clone community set expr shared object
      _expr = cloneCommunityExpr(_expr);

      // add additional assert for using shared object
      if (exprBackup.getEnableSmtVariable() == _expr.getEnableSmtVariable()) {
        throw new BatfishException("DeleteCommunity.initSmtVariable: " +
                "cloning failed for shared object.");
      }
    }

    // assert the isTrue flag is true
    if (true == isTrue) {
      throw new BatfishException("DeleteCommunity.initSmtVariable: invalid is true flag.");
    }

    // init smt variable for community set expr
    _expr.initSmtVariable(context, solver, configVarPrefix, isTrue);

    // configure the smt variable enable flag to true
    _enableSmtVariable = true;
    _configVarPrefix = configVarPrefix;
  }

  public boolean getEnableSmtVariable() {
    return _enableSmtVariable;
  }

  public String getConfigVarPrefix() {
    return _configVarPrefix;
  }
}
