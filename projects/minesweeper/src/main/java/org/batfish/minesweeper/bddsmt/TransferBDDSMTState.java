package org.batfish.minesweeper.bddsmt;

import static com.google.common.base.Preconditions.checkArgument;

import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;

/**
 * The state that is tracked during symbolic BDD-based route analysis: a pair of a {@link
 * TransferParam} and a {@link TransferResult}.
 */
@ParametersAreNonnullByDefault
public class TransferBDDSMTState {

  private final @Nonnull TransferBDDSMTParam _bddsmtParam;
  private final @Nonnull TransferBDDSMTResult _bddsmtResult;

  public TransferBDDSMTState(TransferBDDSMTParam bddsmtParam, TransferBDDSMTResult bddsmtResult) {
    // There should only be one 'active' BDDRoute at any time during symbolic route analysis.
    // Eventually we may want to refactor things so the BDDRoute does not live in both
    // the TransferParam and the TransferResult, but it would require non-trivial updates
    // to the analysis.
    checkArgument(
        bddsmtParam.getData() == bddsmtResult.getReturnValue().getOutputRoute(),
        "TransferBDDSMTParam and TransferBDDSMTReturn should contain the same BDDSMTRoute object");
    _bddsmtParam = bddsmtParam;
    _bddsmtResult = bddsmtResult;
  }

  public TransferBDDSMTParam getTransferParam() {
    return _bddsmtParam;
  }

  public TransferBDDSMTResult getTransferResult() {
    return _bddsmtResult;
  }
}
