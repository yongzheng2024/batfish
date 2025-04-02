package org.batfish.datamodel.routing_policy.expr;

import com.fasterxml.jackson.annotation.JsonTypeInfo;
import java.io.Serializable;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.routing_policy.Environment;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;

@JsonTypeInfo(use = JsonTypeInfo.Id.CLASS, property = "class")
public abstract class PrefixSetExpr implements Serializable {

  @Override
  public abstract boolean equals(Object obj);

  @Override
  public abstract int hashCode();

  public abstract boolean matches(Prefix prefix, Environment environment);

  /** Add configuration constant - SMT symbolic variable */
  public abstract void initSmtVariable(Context context, Solver solver, String configVarPrefix);
}
