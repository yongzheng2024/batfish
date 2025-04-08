package org.batfish.datamodel.routing_policy.expr;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.datamodel.routing_policy.Environment;

public class DecrementMetric extends LongExpr {

  private long _subtrahend;

  @JsonCreator
  private DecrementMetric() {}

  public DecrementMetric(long subtrahend) {
    _subtrahend = subtrahend;

    // initialize enable smt variable flag to false
    _enableSmtVariable = false;
  }

  @Override
  public <T, U> T accept(LongExprVisitor<T, U> visitor, U arg) {
    return visitor.visitDecrementMetric(this, arg);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    DecrementMetric other = (DecrementMetric) obj;
    if (_subtrahend != other._subtrahend) {
      return false;
    }
    return true;
  }

  @Override
  public long evaluate(Environment environment) {
    long oldMetric = environment.getOriginalRoute().getMetric();
    long newVal = Math.max(oldMetric - _subtrahend, 0);
    return newVal;
  }

  public long getSubtrahend() {
    return _subtrahend;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + Long.hashCode(_subtrahend);
    return result;
  }

  public void setSubtrahend(long subtrahend) {
    _subtrahend = subtrahend;
  }

  /** Add configuration constant - SMT symbolic variable */
  private boolean _enableSmtVariable;

  private transient ArithExpr _configVarLocalpreference;

  public void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    if (_enableSmtVariable) {
      return;
    }

    _configVarLocalpreference = context.mkIntConst(configVarPrefix + "localpreference");

    // add relevant configuration constant constraints
    BoolExpr configVarLpConstraint = context.mkEq(
        _configVarLocalpreference, context.mkInt(_subtrahend));
    solver.add(configVarLpConstraint);

    // config enable smt variable flag to true
    _enableSmtVariable = true;
  }

  public boolean getEnableSmtVariable() {
    return _enableSmtVariable;
  }

  public ArithExpr getConfigVarLocalpreference() {
    return _configVarLocalpreference;
  }
}
