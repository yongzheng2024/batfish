package org.batfish.minesweeper.bdd;

import static com.google.common.base.Preconditions.checkArgument;

import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;

/**
 * The state that is tracked during symbolic BDD-based route analysis: a pair of a {@link
 * TransferParam} and a {@link TransferResult}.
 */
@ParametersAreNonnullByDefault
public class TransferBDDState {

  private final @Nonnull TransferParam _param;
  private final @Nonnull TransferResult _result;

  public TransferBDDState(TransferParam param, TransferResult result) {
    // There should only be one 'active' BDDRoute at any time during symbolic route analysis.
    // Eventually we may want to refactor things so the BDDRoute does not live in both
    // the TransferParam and the TransferResult, but it would require non-trivial updates
    // to the analysis.
    checkArgument(
        param.getData() == result.getReturnValue().getOutputRoute(),
        "TransferParam and TransferReturn should contain the same BDDRoute object");
    _param = param;
    _result = result;
  }

  public TransferParam getTransferParam() {
    return _param;
  }

  public TransferResult getTransferResult() {
    return _result;
  }
}
