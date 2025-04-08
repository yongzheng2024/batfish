package org.batfish.datamodel;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonValue;
import java.io.Serializable;
import java.util.Objects;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.batfish.common.BatfishException;

import com.google.common.base.Preconditions;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;

public final class PrefixRange implements Serializable, Comparable<PrefixRange> {

  /** A prefix range representing all prefixes. */
  public static final PrefixRange ALL = fromString("0.0.0.0/0:0-32");

  public PrefixRange(Prefix prefix, SubRange lengthRange) {
    // Canonicalize the prefix by dropping extra bits in the address that are longer than any
    // relevant length.
    int prefixLength = prefix.getPrefixLength();
    int realPrefixLength = Math.min(prefixLength, lengthRange.getEnd());
    if (realPrefixLength == prefixLength) {
      _prefix = prefix;
    } else {
      // FIXME: if prefix or lengthRange have enableSmtVariable flag set to true,
      //        then we should keep same _prefix and _lengthRange with SMT symbolic variable
      //        (maybe we should modify _prefix length and mask SMT symbolic variables)
      //        annotated by yongzheng on 20250407
      Preconditions.checkState(
          false,
          "ERROR: PrefixRange:PrefixRange() " +
          "Prefix and SubRange enabling SMT symbolic variable are not supported");
      Ip realPrefixAddress = prefix.getStartIp().getNetworkAddress(realPrefixLength);
      _prefix = Prefix.create(realPrefixAddress, prefixLength);
    }
    _lengthRange = lengthRange;

    // check Prefix(prefix) and SubRange(lengthRange) enabling SMT symbolic variable flags
    // all flags are true or all flags are false
    Preconditions.checkState(
        (prefix.getEnableSmtVariable() == lengthRange.getEnableSmtVariable()), 
        "ERROR: PrefixRange:PrefixRange() " +
        "Prefix and SubRange enabling SMT symbolic variable are inconsistent");

    if (_prefix.getEnableSmtVariable() && _lengthRange.getEnableSmtVariable()) {
      // configure enable smt variable flag to true according to Prefix and SubRange
      _enableSmtVariable = true;
    } else {
      // initialize enable smt variable flag to false
      _enableSmtVariable = false;
    }
  }

  /** Returns a {@link PrefixRange} that contains exactly the specified {@link Prefix}. */
  public static PrefixRange fromPrefix(Prefix prefix) {
    int prefixLength = prefix.getPrefixLength();
    return new PrefixRange(prefix, SubRange.singleton(prefixLength));
  }

  @JsonCreator
  public static PrefixRange fromString(String prefixRangeStr) {
    String[] parts = prefixRangeStr.split(":");
    if (parts.length == 1) {
      return fromPrefix(Prefix.parse(parts[0]));
    } else if (parts.length == 2) {
      return new PrefixRange(Prefix.parse(parts[0]), new SubRange(parts[1]));
    } else {
      throw new BatfishException("Invalid PrefixRange string: '" + prefixRangeStr + "'");
    }
  }

  /** Returns a {@link PrefixRange} that represents all more specific prefixes. */
  public static PrefixRange moreSpecificThan(Prefix prefix) {
    return new PrefixRange(
        prefix, new SubRange(prefix.getPrefixLength() + 1, Prefix.MAX_PREFIX_LENGTH));
  }

  public SubRange getLengthRange() {
    return _lengthRange;
  }

  public Prefix getPrefix() {
    return _prefix;
  }

  public boolean includesPrefixRange(PrefixRange argPrefixRange) {
    Prefix prefix = getPrefix();
    SubRange lengthRange = getLengthRange();
    int prefixLength = prefix.getPrefixLength();
    long maskedPrefixAsLong = prefix.getStartIp().getNetworkAddress(prefixLength).asLong();
    Prefix argPrefix = argPrefixRange.getPrefix();
    SubRange argLengthRange = argPrefixRange.getLengthRange();
    long argMaskedPrefixAsLong = argPrefix.getStartIp().getNetworkAddress(prefixLength).asLong();
    return maskedPrefixAsLong == argMaskedPrefixAsLong
        && lengthRange.getStart() <= argLengthRange.getStart()
        && lengthRange.getEnd() >= argLengthRange.getEnd();
  }

  @Override
  @JsonValue
  public String toString() {
    int prefixLength = _prefix.getPrefixLength();
    int low = _lengthRange.getStart();
    int high = _lengthRange.getEnd();
    if (prefixLength == low && prefixLength == high) {
      return _prefix.toString();
    } else {
      return _prefix + ":" + low + "-" + high;
    }
  }

  @Override
  public int compareTo(@Nonnull PrefixRange o) {
    int prefixCmp = _prefix.compareTo(o._prefix);
    if (prefixCmp != 0) {
      return prefixCmp;
    }
    return _lengthRange.compareTo(o._lengthRange);
  }

  @Override
  public int hashCode() {
    return Objects.hash(_prefix, _lengthRange);
  }

  @Override
  public boolean equals(@Nullable Object obj) {
    if (obj == this) {
      return true;
    } else if (!(obj instanceof PrefixRange)) {
      return false;
    }
    PrefixRange o = (PrefixRange) obj;
    return _prefix.equals(o._prefix) && _lengthRange.equals(o._lengthRange);
  }

  private final Prefix _prefix;
  private final SubRange _lengthRange;
  
  /** Add configuration constant - SMT symbolic variable */
  private boolean _enableSmtVariable;

  private static String format(String str) {
    String formatedStr = "";
    for (char c : str.toCharArray()) {
      switch (c) {
        case '.':
          formatedStr += '_';
          break;
        default:
          formatedStr += c;
          break;
      }
    }
    return formatedStr;
  }

  private static String longToIpString(long ip) {
    return String.format(
        "%d.%d.%d.%d",
        (ip >> 24) & 0xFF,
        (ip >> 16) & 0xFF,
        (ip >> 8) & 0xFF,
        ip & 0xFF
    );
  }

  public void initSmtVariable(Context context, Solver solver, String configVarPrefix) {
    if (_enableSmtVariable) {
      return;
    }

    long prefixIp = _prefix.getStartIp().asLong();
    String prefixIpStr = longToIpString(prefixIp);
    _prefix.initSmtVariable(context, solver, configVarPrefix + "_" + format(prefixIpStr) + "__");
    _lengthRange.initSmtVariable(
        context, solver, configVarPrefix + "_" + format(prefixIpStr) + "__");

    // configure enable smt variable flag to true
    _enableSmtVariable = true;
  }

  public boolean getEnableSmtVariable() {
    return _enableSmtVariable;
  }
}
