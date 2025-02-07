package org.batfish.common.bddsmt;

import static com.google.common.base.Preconditions.checkArgument;
import static org.batfish.common.bdd.BDDUtils.bitvector;

import org.batfish.common.bdd.MutableBDDInteger;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;
// import org.batfish.datamodel.IpWildcard;

import com.microsoft.z3.Context;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.IntExpr;

public final class MutableBDDSMTInteger extends MutableBDDInteger {
  private Context _context;
  private long _val;

  public MutableBDDSMTInteger(BDDFactory factory, Context context, BDD[] bitvec) {
    super(factory, bitvec);
    _context = context;
    _val = bddArrayToLong(bitvec);
  }

  public MutableBDDSMTInteger(BDDFactory factory, Context context, int length) {
    super(factory, length);
    _context = context;
    _val = 0;
  }

  public MutableBDDSMTInteger(MutableBDDSMTInteger other) {
    this(other._factory, other._context, other.getBDDInteger().length);
    setValue(other);  // set BDDs _bitvec and relevant value _val
  }

  // TODO complete the following methods according to MutableBDDInteger and BDDInteger
  // satAssignmentToInt, satAssignmentToLong, getValueSatisfying, and getValuesSatisfying

  // TODO complete this method according to MutableBDDInteger.java file
  // public final BoolExpr toSMT(IpWildcard ipWildcard);

  // FIXME complete the following methods, /*ite*/, /*and*/, /*sub*/, and allDifferences
 
  /**
   * Create an integer, and initialize its values as "don't care".
   * This requires knowing the start index variables the bitvector will use.
   */
  public static MutableBDDSMTInteger makeFromIndex(
      BDDFactory factory, Context context, int length, int start, boolean reverse) {
    return new MutableBDDSMTInteger(factory, context, 
                                    bitvector(factory, length, start, reverse));
  }

  /** Create an integer and initialize it to a concrete value. */
  public static MutableBDDSMTInteger makeFromValue(
      BDDFactory factory, Context context, int length, long value) {
    MutableBDDSMTInteger bddsmt = new MutableBDDSMTInteger(factory, context, length);
    bddsmt.setValue(value);
    return bddsmt;
  }

  /** Create an integer and initialize it to a maximal value. */
  public static MutableBDDSMTInteger makeMaxValue(
      BDDFactory factory, Context context, int length) {
    MutableBDDSMTInteger bddsmt = new MutableBDDSMTInteger(factory, context, length);
    bddsmt.setValue(bddsmt._maxVal);
    return bddsmt;
  }

  /** Add two BDDs bitwise to create a new BDD. */
  public MutableBDDSMTInteger add(MutableBDDSMTInteger other) {
    BDD[] as = this.getBDDInteger();
    BDD[] bs = other.getBDDInteger();

    checkArgument(as.length > 0, "Cannot add BDDIntegers of length 0");
    checkArgument(as.length == bs.length, "Cannot add BDDIntegers of different length");

    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDSMTInteger sum = new MutableBDDSMTInteger(_factory, _context, as.length);
    BDD carry = _factory.zero();
    BDD[] cs = sum.getBDDInteger();
    for (int i = cs.length - 1; i > 0; --i) {
      cs[i] = as[i].xor(bs[i]).xorEq(carry);
      carry = as[i].and(bs[i]).orWith(as[i].or(bs[i]).andWith(carry));
    }
    cs[0] = carry.xorEq(as[0]).xorEq(bs[0]);
    assertNoLeaks(startBDDCount, _bitvec.length);

    // set long _val according to BDDs _bitvec
    long updatedVal = bddArrayToLong(sum.getBDDInteger());
    sum.setValueInteger(updatedVal);
    return sum;
  }

  /** Add two BDDs bitwise to create a new BDD. Clips to MAX_VALUE in case of overflow. */
  public MutableBDDSMTInteger addClipping(MutableBDDSMTInteger other) {
    BDD[] as = this.getBDDInteger();
    BDD[] bs = other.getBDDInteger();

    checkArgument(as.length > 0, "Cannot add BDDIntegers of length 0");
    checkArgument(as.length == bs.length, "Cannot add BDDIntegers of different length");

    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDSMTInteger sum = new MutableBDDSMTInteger(_factory, _context, as.length);
    BDD[] cs = sum.getBDDInteger();
    BDD carry = _factory.zero();
    for (int i = cs.length - 1; i >= 0; --i) {
      cs[i] = as[i].xor(bs[i]).xorEq(carry);
      carry = as[i].and(bs[i]).orWith(carry.andWith(as[i].or(bs[i])));
    }
    MutableBDDSMTInteger maxValue = makeMaxValue(_factory, _context, as.length);
    MutableBDDSMTInteger result = sum.ite(carry.notEq(), maxValue);
    maxValue.free();
    sum.free();
    carry.free();
    assertNoLeaks(startBDDCount, _bitvec.length);

    // set long _val according to BDDs _bitvec
    long updatedVal = bddArrayToLong(result.getBDDInteger());
    result.setValueInteger(updatedVal);
    return result;
  }

  /** Assert outstanding BDDs number in BDDFactory. */
  private void assertNoLeaks(long startBDDs, long incremental) {
    assert _factory.numOutstandingBDDs() == startBDDs + incremental
        : String.format(
            "Expected to create %d new BDDs, actually created %d",
            incremental, _factory.numOutstandingBDDs() - startBDDs);
  }

  /** Execute 'ite(this, b, other)' bitwise operation to create a new BDDSMT object. */
  public MutableBDDSMTInteger ite(BDD b, MutableBDDSMTInteger other) {
    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDSMTInteger bddsmt = 
        new MutableBDDSMTInteger(_factory, _context, _bitvec.length);
    for (int i = 0; i < _bitvec.length; i++) {
      bddsmt._bitvec[i] = b.ite(_bitvec[i], other.getBDDInteger()[i]);
    }
    assertNoLeaks(startBDDCount, _bitvec.length);

    // set value integer according to the result of BDDs _bitvec
    bddsmt.setValueInteger(MutableBDDSMTInteger.bddArrayToLong(bddsmt._bitvec));
    return bddsmt;
  }

  /** And a restrictation pred BDD and return a new BDDSMT object. */
  public MutableBDDSMTInteger and(BDD pred) {
    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDSMTInteger bddsmt = 
        new MutableBDDSMTInteger(_factory, _context, _bitvec.length);
    for (int i = 0; i < _bitvec.length; i++) {
      bddsmt._bitvec[i] = pred.and(_bitvec[i]);
    }
    assertNoLeaks(startBDDCount, _bitvec.length);

    // set value integer according to the result of BDDs _bitvec
    bddsmt.setValueInteger(MutableBDDSMTInteger.bddArrayToLong(bddsmt._bitvec));
    return bddsmt;
  }

  /** Subtract one BDD from another bitwise to create a new BDDSMT object. */
  public MutableBDDSMTInteger sub(MutableBDDSMTInteger other) {
    checkArgument(this.getBDDInteger().length == other.getBDDInteger().length, 
                  "Input variable must have equal bitvector length");

    int length = _bitvec.length;
    long startBDDCount = _factory.numOutstandingBDDs();
    BDD[] a = this.getBDDInteger();
    BDD[] b = other.getBDDInteger();
    MutableBDDSMTInteger bddsmt = new MutableBDDSMTInteger(_factory, _context, length);
    BDD[] c = bddsmt.getBDDInteger(); // We will compute c = a - b.
    BDD borrow = _factory.zero(); // the opposite of carry
    for (int i = length - 1; i >= 0; --i) {
      c[i] = a[i].xor(b[i]).xorEq(borrow);
      BDD var7 = b[i].or(borrow).diffEq(a[i]);
      borrow = a[i].and(b[i]).andWith(borrow).orWith(var7);
    }
    borrow.free();
    assertNoLeaks(startBDDCount, this.getBDDInteger().length);

    // set value integer according to the result of BDDs _bitvec
    bddsmt.setValueInteger(MutableBDDSMTInteger.bddArrayToLong(bddsmt.getBDDInteger()));
    return bddsmt;
  }

  /** Set all the component (BDDs _bitvec and value _val) according to another BDD. */
  public void setValue(MutableBDDSMTInteger other) {
    for (int i = 0; i < _bitvec.length; ++i) {
      _bitvec[i] = other._bitvec[i].id();
    }
    _val = bddArrayToLong(other._bitvec);
  }

  /** Set all the component (BDDs _bitvec and value _val) to have an exact value. */
  public void setValue(long val) {
    checkArgument(val >= 0, "Cannot set a negative value");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);
    long currentVal = val;
    for (int i = _bitvec.length - 1; i >= 0; --i) {
      if ((currentVal & 1) != 0) {
        _bitvec[i] = _factory.one();
      } else {
        _bitvec[i] = _factory.zero();
      }
      currentVal >>= 1;
    }
    _val = val;
  }

  /** Free all the component (BDDs _bitvec and value _val) in this object. */
  public void free() {
    for (int i = 0; i < _bitvec.length; ++i) {
      _bitvec[i].free();
      _bitvec[i] = null;
    }
    _val = 0;
  }

  /** Build a constraint that matches the set of IPs contained by the input {@link Prefix}. */
  public BoolExpr toSMT(Prefix prefix, String configName, String exprName) {
    checkArgument(
        _bitvec.length == Prefix.MAX_PREFIX_LENGTH,
        "toBDD(Prefix) requires %s bits",
        Prefix.MAX_PREFIX_LENGTH);

    // 10.0.0.0/8     -> beginIp is 10.0.0.0,    endIp is 10.255.255.255
    // 172.16.0.0/12  -> beginIp is 172.16.0.0,  endIp is 172.31.255.255
    // 192.168.0.0/16 -> beginIp is 192.168.0.0, endIp is 192.168.255.255
    long beginIp = prefix.getStartIp().asLong();
    int prefixLength = prefix.getPrefixLength();
    long suffixEndIp = (1 << (32 - prefixLength)) - 1;
    long endIp = beginIp | suffixEndIp;
    return rangeSmt(beginIp, endIp, configName, exprName);
  }

  public BDDSMT toBDDSMT(Prefix prefix, String configName, String exprName) {
    BDD bdd = toBDD(prefix);
    BoolExpr smt = toSMT(prefix, configName, exprName);
    return new BDDSMT(bdd, smt);
  }

  /** Build a constraint that matches the input {@link Ip}. */
  public BoolExpr toSMT(Ip ip, String configName, String exprName) {
    checkArgument(
        _bitvec.length == Prefix.MAX_PREFIX_LENGTH,
        "toBDD(Ip) requires %s bits",
        Prefix.MAX_PREFIX_LENGTH);

    return valueSmt(ip.asLong(), configName, exprName);
  }

  public BDDSMT toBDDSMT(Ip ip, String configName, String exprName) {
    BDD bdd = toBDD(ip);
    BoolExpr smt = toSMT(ip, configName, exprName);
    return new BDDSMT(bdd, smt);
  }

  // FIXME the method name singleEqual -> valueSmt
  /** Create a SMT BoolExpr representing the exact value. */
  public BoolExpr valueSmt(long val, String configName, String exprName) {
    checkArgument(val >= 0, "value is negative");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);

    // configVar == val AND exprVar == configVar

    IntExpr  smtConfigVar = _context.mkIntConst(configName);
    IntExpr  smtMatchVar  = _context.mkIntConst(exprName);
    BoolExpr smtConfigEq  = _context.mkEq(smtConfigVar, _context.mkInt(val));
    BoolExpr smtExprEq    = _context.mkEq(smtMatchVar, smtConfigVar);
    BoolExpr smtSingle    = _context.mkAnd(smtConfigEq, smtExprEq);

    return smtSingle;
  }

  public BDDSMT valueBddsmt(long val, String configName, String exprName) {
    BDD bdd = value(val);
    BoolExpr smt = valueSmt(val, configName, exprName);
    return new BDDSMT(bdd, smt);
  }

  // FIXME the method name rangeEqual -> rangeSmt
  /** Integers in the given range, inclusive, where {@code a} is less than or equal to {@code b}. */
  public BoolExpr rangeSmt(long begVal, long endVal, String configName, String exprName) {
    checkArgument(begVal <= endVal, "range is not ordered correctly");
    checkArgument(begVal >= 0, "value is negative");
    checkArgument(endVal <= _maxVal, "value %s is out of range [0, %s]", endVal, _maxVal);

    if (begVal == endVal) {
      return valueSmt(begVal, configName, exprName);
    }

    // ( configVar >= begVal AND configVar <= endVal ) AND exprVar == configVar

    String configNameBeginSuffix = "_begin";
    String configNameEndSuffix   = "_end";

    // IntExpr  smtConfigVar = _context.mkIntConst(configName);
    IntExpr  smtConfigVarBegin = _context.mkIntConst(configName + configNameBeginSuffix);
    IntExpr  smtConfigVarEnd   = _context.mkIntConst(configName + configNameEndSuffix);
    IntExpr  smtMatchVar  = _context.mkIntConst(exprName);
    // BoolExpr smtConfigRng = _context.mkAnd(
    //     _context.mkGe(smtConfigVar, _context.mkInt(begVal)),
    //     _context.mkLe(smtConfigVar, _context.mkInt(endVal))
    // );
    // BoolExpr smtExprRng   = _context.mkEq(smtExprVar, smtConfigVar);
    BoolExpr smtConfigRng = _context.mkAnd(
        _context.mkEq(smtConfigVarBegin, _context.mkInt(begVal)),
        _context.mkEq(smtConfigVarEnd,   _context.mkInt(endVal))
    );
    BoolExpr smtExprRng   = _context.mkAnd(
        _context.mkGe(smtMatchVar, smtConfigVarBegin), 
        _context.mkLe(smtMatchVar, smtConfigVarEnd)
    );
    BoolExpr smtRange     = _context.mkAnd(smtConfigRng, smtExprRng);

    return smtRange;
  }

  public BDDSMT rangeBddsmt(long begVal, long endVal, String configName, String exprName) {
    BDD bdd = range(begVal, endVal);
    BoolExpr smt = rangeSmt(begVal, endVal, configName, exprName);
    return new BDDSMT(bdd, smt);
  }

  /** Less than or equal to on integers. */
  public BoolExpr leqSmt(long val, String configName, String exprName) {
    checkArgument(val >= 0, "value is negative");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);

    // configVar <= val AND exprVar == configVar

    IntExpr  smtConfigVar = _context.mkIntConst(configName);
    IntExpr  smtMatchVar  = _context.mkIntConst(exprName);
    // BoolExpr smtConfigLeq = _context.mkLe(smtConfigVar, _context.mkInt(val));
    // BoolExpr smtExprLeq   = _context.mkEq(smtMatchVar, smtConfigVar);
    BoolExpr smtConfigLeq = _context.mkEq(smtConfigVar, _context.mkInt(val));
    BoolExpr smtExprLeq   = _context.mkLe(smtMatchVar, smtConfigVar);
    BoolExpr smtLeq       = _context.mkAnd(smtConfigLeq, smtExprLeq);

    return smtLeq;
  }

  /** Greater than or equal to on integers. */
  public BoolExpr geqSmt(long val, String configName, String exprName) {
    checkArgument(val >= 0, "value is negative");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);

    // configVar >= val AND exprVar == configVar

    IntExpr  smtConfigVar = _context.mkIntConst(configName);
    IntExpr  smtMatchVar  = _context.mkIntConst(exprName);
    // BoolExpr smtConfigGeq = _context.mkGe(smtConfigVar, _context.mkInt(val));
    // BoolExpr smtExprGeq   = _context.mkEq(smtMatchVar, smtConfigVar);
    BoolExpr smtConfigGeq = _context.mkEq(smtConfigVar, _context.mkInt(val));
    BoolExpr smtExprGeq   = _context.mkGe(smtMatchVar, smtConfigVar);
    BoolExpr smtGeq       = _context.mkAnd(smtConfigGeq, smtExprGeq);

    return smtGeq;
  }                                                  

  /** Convert an array of BDDs to a long value. */
  public static long bddArrayToLong(BDD[] bitvec) {
    long result = 0;

    // Iterate over the BDD array and combine them into a long value
    for (int i = 0; i < bitvec.length; ++i) {
      // Evaluate the BDD (true = 1, false = 0) and shift accordingly
      boolean bit = bitvec[i].isOne();
      result = (result << 1) | (bit ? 1 : 0); // shift and set the bit
    }

    return result; 
  }

  public Context getContext() {
    return _context;
  }

  public BDD[] getBDDInteger() {
    return super._bitvec;
  }

  public long getValueInteger() {
    return _val;
  }

  public void setValueInteger(long val) {
    _val = val;
  }
}
