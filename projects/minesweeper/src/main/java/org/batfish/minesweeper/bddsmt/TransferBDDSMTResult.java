package org.batfish.minesweeper.bddsmt;

import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;
import net.sf.javabdd.BDD;

import org.batfish.common.bddsmt.BDDSMT;

import com.microsoft.z3.BoolExpr;


/**
 * This class is used to keep track of the state of the BDD-based symbolic control-plane analysis in
 * {@link TransferBDD}. It's effectively the symbolic version of {@link
 * org.batfish.datamodel.routing_policy.Result} but represents the result along one particular path
 * through the route policy.
 */
@ParametersAreNonnullByDefault
public class TransferBDDSMTResult {

  /**
   * the symbolic route information that is ultimately returned as the result of the analysis: a
   * triple of a BDDRoute, which represents this path's output announcement as a function of the
   * input announcement; a BDD, which represents the conditions under which this particular path is
   * taken; and a boolean indicating whether the path ultimately accepts or rejects the announcement
   */
  // private final @Nonnull TransferReturn _returnValue;
  private final @Nonnull TransferBDDSMTReturn _returnBddsmtValue;

  /**
   * Whether the routes that go down this path should be suppressed (i.e., not announced). Route
   * suppression happens due to aggregation, and this is represented by the {@link
   * org.batfish.datamodel.routing_policy.statement.Statements.StaticStatement} Suppress, but routes
   * can also be explicitly unsuppressed with Unsuppress.
   */
  private final boolean _suppressedValue;

  /**
   * The following three fields are used to ensure that the analysis accurately identifies all and
   * only feasible execution paths through a route policy.
   */

  /* boolean indicating that the analysis has hit a fall-through condition in the policy
  being analyzed, meaning that control flow should continue to the next policy */
  private final boolean _fallthroughValue;

  /* boolean indicating that the analysis has hit an exit condition in the policy
  being analyzed, which represents the termination of the execution */
  private final boolean _exitAssignedValue;

  /* boolean indicating that the analysis has hit a return condition in the policy
  being analyzed, which represents the termination of a nested call to a routing policy */
  private final boolean _returnAssignedValue;

  /**
   * Construct a TransferBDDSMTResult from a BDDRoute. By default we use TRUE as the initial path
   * condition and FALSE as the initial value for having hit a return/exit/fallthrough statement.
   */
  public TransferBDDSMTResult(BDDSMTRoute bddsmtRoute) {
    this(new TransferBDDSMTReturn(bddsmtRoute, bddsmtRoute.getFactory().one(),
                                  bddsmtRoute.getContext().mkTrue(), false),
         false,
         false,
         false,
         false);
  }

  public TransferBDDSMTResult(
      TransferBDDSMTReturn returnBddsmtValue,
      boolean suppressedValue,
      boolean exitAssignedValue,
      boolean fallThroughValue,
      boolean returnAssignedValue) {
    _returnBddsmtValue = returnBddsmtValue;
    _suppressedValue = suppressedValue;
    _exitAssignedValue = exitAssignedValue;
    _fallthroughValue = fallThroughValue;
    _returnAssignedValue = returnAssignedValue;
  }

  public @Nonnull TransferBDDSMTReturn getReturnValue() {
    return _returnBddsmtValue;
  }

  public boolean getSuppressedValue() {
    return _suppressedValue;
  }

  public boolean getFallthroughValue() {
    return _fallthroughValue;
  }

  public boolean getExitAssignedValue() {
    return _exitAssignedValue;
  }

  public boolean getReturnAssignedValue() {
    return _returnAssignedValue;
  }

  public @Nonnull TransferBDDSMTResult setReturnValue(TransferBDDSMTReturn newbddsmtReturn) {
    return new TransferBDDSMTResult(newbddsmtReturn, _suppressedValue, _exitAssignedValue,
                                    _fallthroughValue, _returnAssignedValue);
  }

  public @Nonnull TransferBDDSMTResult setReturnValueAccepted(boolean newAccepted) {
    return setReturnValue(_returnBddsmtValue.setAccepted(newAccepted));
  }

  public @Nonnull TransferBDDSMTResult setReturnValueBDD(BDD newBdd) {
    return setReturnValue(
        new TransferBDDSMTReturn(_returnBddsmtValue.getOutputRoute(),
                                 newBdd,
                                 _returnBddsmtValue.getInputSmtConstraints(), 
                                 _returnBddsmtValue.getAccepted()));
  }

  public @Nonnull TransferBDDSMTResult setReturnValueSMT(BoolExpr newSmt) {
    return setReturnValue(
        new TransferBDDSMTReturn(_returnBddsmtValue.getOutputRoute(), 
                                 _returnBddsmtValue.getInputConstraints(), 
                                 newSmt, 
                                 _returnBddsmtValue.getAccepted()));
  }

  public @Nonnull TransferBDDSMTResult setReturnValueBDDSMT(BDD newBdd, BoolExpr newSmt) {
    return setReturnValue(
        new TransferBDDSMTReturn(_returnBddsmtValue.getOutputRoute(), 
                                 newBdd,
                                 newSmt, 
                                 _returnBddsmtValue.getAccepted()));
  }

  public @Nonnull TransferBDDSMTResult setReturnValueBDDSMT(BDDSMT newBddsmt) {
    return setReturnValue(
        new TransferBDDSMTReturn(_returnBddsmtValue.getOutputRoute(),
                                 newBddsmt.getBddVariable(),
                                 newBddsmt.getSmtVariable(),
                                 _returnBddsmtValue.getAccepted()));
  }

  public @Nonnull TransferBDDSMTResult setReturnValueBDDRoute(BDDSMTRoute newBddsmtRoute) {
    return setReturnValue(
        new TransferBDDSMTReturn(newBddsmtRoute, 
                                 _returnBddsmtValue.getInputConstraints(), 
                                 _returnBddsmtValue.getInputSmtConstraints(), 
                                 _returnBddsmtValue.getAccepted()));
  }

  public @Nonnull TransferBDDSMTResult setSuppressedValue(boolean suppressedValue) {
    return new TransferBDDSMTResult(_returnBddsmtValue, suppressedValue, 
                                    _exitAssignedValue, _fallthroughValue, _returnAssignedValue);
  }

  public @Nonnull TransferBDDSMTResult setExitAssignedValue(boolean exitAssignedValue) {
    return new TransferBDDSMTResult(_returnBddsmtValue, _suppressedValue, 
                                    exitAssignedValue, _fallthroughValue, _returnAssignedValue);
  }

  public @Nonnull TransferBDDSMTResult setFallthroughValue(boolean fallthroughValue) {
    return new TransferBDDSMTResult(_returnBddsmtValue, _suppressedValue, 
                                    _exitAssignedValue, fallthroughValue, _returnAssignedValue);
  }

  public @Nonnull TransferBDDSMTResult setReturnAssignedValue(boolean returnAssignedValue) {
    return new TransferBDDSMTResult(_returnBddsmtValue, _suppressedValue, 
                                    _exitAssignedValue, _fallthroughValue, returnAssignedValue);
  }
}
