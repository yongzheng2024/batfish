package org.batfish.minesweeper.expr;

import org.batfish.datamodel.routing_policy.expr.ExplicitPrefixSet;
import org.batfish.datamodel.PrefixSpace;

public class SmtExplicitPrefixSet extends ExplicitPrefixSet {
  public SmtExplicitPrefixSet(PrefixSpace prefixSpace) {
    super(prefixSpace);
  }
}
