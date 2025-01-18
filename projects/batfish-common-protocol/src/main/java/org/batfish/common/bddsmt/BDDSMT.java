package org.batfish.common.bddsmt;

import net.sf.javabdd.BDD;
import com.microsoft.z3.BoolExpr;

public final class BDDSMT {
  private BDD _bddVar;
  private BoolExpr _smtVar;

  public BDDSMT(BDD bddVar, BoolExpr smtVar) {
    _bddVar = bddVar;
    _smtVar = smtVar;
  }

  public BDD getBddVariable() {
    return _bddVar;
  }

  public BoolExpr getSmtVariable() {
    return _smtVar;
  }

  public void setBddVariable(BDD bddVar) {
    _bddVar = bddVar;
  }

  public void setSmtVariable(BoolExpr smtVar) {
    _smtVar = smtVar;
  }
}
