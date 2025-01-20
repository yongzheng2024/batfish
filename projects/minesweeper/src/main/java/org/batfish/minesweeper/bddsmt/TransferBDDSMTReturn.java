package org.batfish.minesweeper.bddsmt;

import java.util.Objects;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import net.sf.javabdd.BDD;

import com.microsoft.z3.BoolExpr;


/**
 * The data produced by the symbolic route policy analysis performed in {@link TransferBDD}. It is a
 * triple representing the analysis results along a particular execution path through the route
 * policy:
 *
 * <p>1. A {@link BDDRoute} that represents a function from an input announcement to the
 * corresponding output announcement produced by the analyzed route policy on this particular path.
 * Note that even if the path ends up rejecting the given route, we still record all route updates
 * that occur. We also record whether the path encountered a statement that the {@link TransferBDD}
 * analysis does not currently support, which indicates that the analysis results may not be
 * accurate.
 *
 * <p>2. A {@link BDD} that represents the set of input announcements that take this particular
 * path.
 *
 * <p>3. A boolean indicating whether the path accepts or rejects the input announcement.
 */
@ParametersAreNonnullByDefault
public final class TransferBDDSMTReturn {
  // private final @Nonnull BDDRoute _outputRoute;
  private final @Nonnull BDDSMTRoute _outputRoute;
  private final @Nonnull BDD _inputConstraints;
  private final @Nonnull BoolExpr _inputSmtConstraints;
  private final boolean _accepted;

  TransferBDDSMTReturn(BDDSMTRoute outputRoute, BDD inputConstraints, BoolExpr inputSmtConstraints, boolean accepted) {
    _outputRoute = outputRoute;
    _inputConstraints = inputConstraints;
    _inputSmtConstraints = inputSmtConstraints;
    _accepted = accepted;
  }

  public @Nonnull BDDSMTRoute getOutputRoute() {
    return _outputRoute;
  }

  public @Nonnull BDD getInputConstraints() {
    return _inputConstraints;
  }

  public @Nonnull BoolExpr getInputSmtConstraints() {
    return _inputSmtConstraints;
  }

  public boolean getAccepted() {
    return _accepted;
  }

  public TransferBDDSMTReturn setAccepted(boolean accepted) {
    return new TransferBDDSMTReturn(_outputRoute, _inputConstraints, _inputSmtConstraints, accepted);
  }

  public String debug() {
    return _outputRoute.dot(_inputConstraints);
  }

  @Override
  public boolean equals(@Nullable Object o) {
    if (o == this) {
      return true;
    } else if (o == null || !(o instanceof TransferBDDSMTReturn)) {
      return false;
    }
    TransferBDDSMTReturn other = (TransferBDDSMTReturn) o;
    return this._outputRoute.equals(other._outputRoute)
        && this._inputConstraints.equals(other._inputConstraints)
        && this._inputSmtConstraints.equals(other._inputSmtConstraints)
        && this._accepted == other._accepted;
  }

  @Override
  public int hashCode() {
    return Objects.hash(_outputRoute, _inputConstraints, _inputSmtConstraints, _accepted);
  }

  @Override
  public String toString() {
    return "<" + _outputRoute + "," + _inputConstraints + "," + _inputSmtConstraints + 
           "," + _accepted + ">";
  }
}
