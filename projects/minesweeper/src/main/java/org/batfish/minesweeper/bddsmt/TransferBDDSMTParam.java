package org.batfish.minesweeper.bddsmt;

// import com.google.errorprone.annotations.FormatMethod;
import javax.annotation.Nullable;
import org.batfish.datamodel.routing_policy.statement.SetDefaultPolicy;
import org.batfish.minesweeper.collections.PList;


public class TransferBDDSMTParam {
  public enum CallContext {
    EXPR_CALL,
    STMT_CALL,
    NONE
  }

  public enum ChainContext {
    CONJUNCTION,
    DISJUNCTION,
    NONE
  }

  private BDDSMTRoute _data;

  private int _indent;

  private PList<String> _scopes;

  private CallContext _callContext;

  private ChainContext _chainContext;

  private boolean _defaultAccept;

  private boolean _defaultAcceptLocal;

  private SetDefaultPolicy _defaultPolicy;

  private boolean _readIntermediateBgpAttributes;

  private final boolean _debug;

  public TransferBDDSMTParam(BDDSMTRoute data, boolean debug) {
    _data = data;
    _callContext = CallContext.NONE;
    _chainContext = ChainContext.NONE;
    _indent = 0;
    _scopes = PList.empty();
    _defaultAccept = false;
    _defaultAcceptLocal = false;
    _defaultPolicy = null;
    _readIntermediateBgpAttributes = false;
    _debug = debug;
  }

  private TransferBDDSMTParam(TransferBDDSMTParam p) {
    _data = p._data;
    _callContext = p._callContext;
    _chainContext = p._chainContext;
    _indent = p._indent;
    _scopes = p._scopes;
    _defaultAccept = p._defaultAccept;
    _defaultAcceptLocal = p._defaultAcceptLocal;
    _defaultPolicy = p._defaultPolicy;
    _readIntermediateBgpAttributes = p._readIntermediateBgpAttributes;
    _debug = p._debug;
  }

  public BDDSMTRoute getData() {
    return _data;
  }

  public CallContext getCallContext() {
    return _callContext;
  }

  public ChainContext getChainContext() {
    return _chainContext;
  }

  public boolean getDefaultAccept() {
    return _defaultAccept;
  }

  public boolean getDefaultAcceptLocal() {
    return _defaultAcceptLocal;
  }

  public SetDefaultPolicy getDefaultPolicy() {
    return _defaultPolicy;
  }

  public boolean getReadIntermediateBgpAtttributes() {
    return _readIntermediateBgpAttributes;
  }

  public boolean getInitialCall() {
    return _indent == 0;
  }

  public String getScope() {
    return _scopes.get(0);
  }

  public TransferBDDSMTParam deepCopy() {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._data = ret._data.deepCopy();
    return ret;
  }

  public TransferBDDSMTParam setData(BDDSMTRoute other) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._data = other;
    return ret;
  }

  public TransferBDDSMTParam setCallContext(CallContext cc) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._callContext = cc;
    return ret;
  }

  public TransferBDDSMTParam setChainContext(ChainContext cc) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._chainContext = cc;
    return ret;
  }

  public TransferBDDSMTParam setDefaultAccept(boolean defaultAccept) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._defaultAccept = defaultAccept;
    return ret;
  }

  public TransferBDDSMTParam setDefaultPolicy(@Nullable SetDefaultPolicy defaultPolicy) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._defaultPolicy = defaultPolicy;
    return ret;
  }

  public TransferBDDSMTParam setDefaultAcceptLocal(boolean defaultAcceptLocal) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._defaultAcceptLocal = defaultAcceptLocal;
    return ret;
  }

  public TransferBDDSMTParam setDefaultActionsFrom(TransferBDDSMTParam updatedParam) {
    return setDefaultAccept(updatedParam._defaultAccept)
        .setDefaultAcceptLocal(updatedParam._defaultAcceptLocal);
  }

  public TransferBDDSMTParam setReadIntermediateBgpAttributes(boolean b) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._readIntermediateBgpAttributes = b;
    return ret;
  }

  public TransferBDDSMTParam enterScope(String name) {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._scopes = ret._scopes.plus(name);
    return ret;
  }

  public TransferBDDSMTParam indent() {
    TransferBDDSMTParam ret = new TransferBDDSMTParam(this);
    ret._indent = _indent + 1;
    return ret;
  }

  public int getIndent() {
    return _indent;
  }

  public String getDebug(String fmt, Object... args) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < _indent; i++) {
      sb.append("    ");
    }
    String s = _scopes.get(0);
    String scope = (s == null ? "" : s);
    sb.append("[");
    sb.append(scope);
    sb.append("]: ");
    sb.append(String.format(fmt, args));
    return sb.toString();
  }

  /* @FormatMethod */
  public void debug(String fmt, Object... args) {
    if (_debug) {
      StringBuilder sb = new StringBuilder();
      for (int i = 0; i < _indent; i++) {
        sb.append("    ");
      }
      String s = _scopes.get(0);
      String scope = (s == null ? "" : s);
      sb.append("[");
      sb.append(scope);
      sb.append("]: ");
      sb.append(String.format(fmt, args));
      System.out.println(sb);
    }
  }
}
