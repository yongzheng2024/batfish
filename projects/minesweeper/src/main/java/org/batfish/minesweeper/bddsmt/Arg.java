package org.batfish.minesweeper.bddsmt;

import javax.annotation.Nonnull;

// a tuple of a TransferBDD object and a BDDRoute object, used as the argument to this visitor
public /*static*/ class Arg {
  private final @Nonnull TransferBDDSMT _transferBDD;
  private final @Nonnull BDDSMTRoute _bddRoute;

  public Arg(TransferBDDSMT transferBDD, BDDSMTRoute bddRoute) {
    _transferBDD = transferBDD;
    _bddRoute = bddRoute;
  }

  TransferBDDSMT getTransferBDD() {
    return _transferBDD;
  }

  BDDSMTRoute getBDDRoute() {
    return _bddRoute;
  }
}
