package org.batfish.common.bddsmt;

import static com.google.common.base.Preconditions.checkArgument;
import static org.batfish.common.bdd.BDDUtils.bitvector;

import org.batfish.common.bdd.MutableBDDInteger;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;

import com.microsoft.z3.Context;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.IntExpr;

public final class MutableBDDSMTInteger extends MutableBDDInteger {
  public MutableBDDSMTInteger(BDDFactory factory, BDD[] bitvec) {
    super(factory, bitvec);
  }

  public MutableBDDSMTInteger(BDDFactory factory, int length) {
    super(factory, length);
  }

  public MutableBDDSMTInteger(MutableBDDSMTInteger other) {
    super(other);
  }

  /** Build a constraint that matches the set of IPs contained by the input {@link Prefix}. */
  public final BoolExpr toSMT(Prefix prefix, Context context, String exprName) {
    checkArgument(
        _bitvec.length == Prefix.MAX_PREFIX_LENGTH,
        "toBDD(Prefix) requires %s bits",
        Prefix.MAX_PREFIX_LENGTH);

    // 192.168.0.0/16 -> startIp is 192.168.0.0, endIp is 192.168.255.255
    long startIp = prefix.getStartIp().asLong();
    int prefixLength = prefix.getPrefixLength();
    long suffixEndIp = (1 << prefixLength) - 1;
    long endIp = startIp | suffixEndIp;
    return rangeEqual(startIp, endIp, context, exprName);
  }

  /** Build a constraint that matches the input {@link Ip}. */
  public final BoolExpr toSMT(Ip ip, Context context, String exprName) {
    checkArgument(
        _bitvec.length == Prefix.MAX_PREFIX_LENGTH,
        "toBDD(Ip) requires %s bits",
        Prefix.MAX_PREFIX_LENGTH);

    return singleEqual(ip.asLong(), context, exprName);
  }

  /**
   * Create an integer, and initialize its values as "don't care" This requires knowing the start
   * index variables the bitvector will use.
   */
  public static MutableBDDSMTInteger makeFromIndex(
      BDDFactory factory, int length, int start, boolean reverse) {
    return new MutableBDDSMTInteger(factory, bitvector(factory, length, start, reverse));
  }

  public final BoolExpr singleEqual(long val, Context context, String exprName) {
    checkArgument(val >= 0, "value is negative");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);

    IntExpr smtVal = context.mkIntConst(exprName);
    BoolExpr smtSingle = context.mkEq(smtVal, context.mkInt(val));

    return smtSingle;
  }

  public final BoolExpr rangeEqual(long begVal, long endVal, Context context, String exprName) {
    checkArgument(begVal <= endVal, "range is not ordered correctly");
    checkArgument(begVal >= 0, "value is negative");
    checkArgument(endVal <= _maxVal, "value %s is out of range [0, %s]", endVal, _maxVal);

    if (begVal == endVal) {
      return singleEqual(begVal, context, exprName);
    }

    IntExpr smtVal = context.mkIntConst(exprName);
    BoolExpr smtRange = context.mkAnd(
        context.mkGe(smtVal, context.mkInt(begVal)),
        context.mkLe(smtVal, context.mkInt(endVal))
    );

    return smtRange;
  }
}
