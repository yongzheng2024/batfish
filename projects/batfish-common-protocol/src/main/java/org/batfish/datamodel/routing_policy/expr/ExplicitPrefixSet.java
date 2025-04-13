package org.batfish.datamodel.routing_policy.expr;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.Environment;

public class ExplicitPrefixSet extends PrefixSetExpr {
  private static final String PROP_PREFIX_SPACE = "prefixSpace";

  private PrefixSpace _prefixSpace;

  @JsonCreator
  private ExplicitPrefixSet() {}

  public ExplicitPrefixSet(PrefixSpace prefixSpace) {
    _prefixSpace = prefixSpace;

    // initialize enable smt variable flag to false
    _enableSmtVariable = false;
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
    ExplicitPrefixSet other = (ExplicitPrefixSet) obj;
    if (_prefixSpace == null) {
      if (other._prefixSpace != null) {
        return false;
      }
    } else if (!_prefixSpace.equals(other._prefixSpace)) {
      return false;
    }
    return true;
  }

  @JsonProperty(PROP_PREFIX_SPACE)
  public PrefixSpace getPrefixSpace() {
    return _prefixSpace;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((_prefixSpace == null) ? 0 : _prefixSpace.hashCode());
    return result;
  }

  @Override
  public boolean matches(Prefix prefix, Environment environment) {
    boolean value = _prefixSpace.containsPrefix(prefix);
    return value;
  }

  @JsonProperty(PROP_PREFIX_SPACE)
  public void setPrefixSpace(PrefixSpace prefixSpace) {
    _prefixSpace = prefixSpace;
  }

  /** Add configuration constant - SMT symbolic variable */
  private boolean _enableSmtVariable;
  private String _configVarPrefix;

  @Override
  public final void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    // assert that the prefix set is not shared
    if (_enableSmtVariable) {
      System.out.println("ERROR ExplicitPrefixSet:initSmtVariable");
      System.out.println("Previous configVarPrefix: " + _configVarPrefix);
      System.out.println("Current  configVarPrefix: " + configVarPrefix);
      return;
    }

    // check and avoid shared object
    if (_prefixSpace.getEnableSmtVariable()) {
      PrefixSpace prefixSpaceBackup = _prefixSpace;
      _prefixSpace = new PrefixSpace(_prefixSpace.getPrefixRanges());

      // add additional assert for using shared object
      // if (prefixSpaceBackup == _prefixSpace) {
      if (prefixSpaceBackup.getEnableSmtVariable() == _prefixSpace.getEnableSmtVariable()) {
        throw new BatfishException("ERROR ExplicitPrefixSet:initSmtVariable use shared object");
      }
    }

    // init smt variable for prefix set configuration
    _prefixSpace.initSmtVariable(context, solver, configVarPrefix);

    // configure the enable smt variable flag to true
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
