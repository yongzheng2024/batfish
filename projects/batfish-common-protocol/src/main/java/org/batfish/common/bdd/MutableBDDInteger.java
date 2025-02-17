package org.batfish.common.bdd;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.batfish.common.bdd.BDDUtils.bitvector;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.IpWildcard;
import org.batfish.datamodel.Prefix;

public /*final*/ class MutableBDDInteger extends BDDInteger {
  // Temporary ArrayLists used to optimize some internal computations.
  private transient List<BDD> _trues;
  private transient List<BDD> _falses;

  public MutableBDDInteger(BDDFactory factory, BDD[] bitvec) {
    super(factory, bitvec);
    initTransientFields();
  }

  public MutableBDDInteger(BDDFactory factory, int length) {
    this(factory, new BDD[length]);
  }

  public MutableBDDInteger(MutableBDDInteger other) {
    this(other._factory, other._bitvec.length);
    setValue(other);
  }

  private void readObject(java.io.ObjectInputStream stream)
      throws IOException, ClassNotFoundException {
    stream.defaultReadObject();
    initTransientFields();
  }

  private void initTransientFields() {
    _trues = new ArrayList<>(_bitvec.length);
    _falses = new ArrayList<>(_bitvec.length);
  }

  /**
   * Create an integer, and initialize its values as "don't care" This requires knowing the start
   * index variables the bitvector will use.
   */
  public static MutableBDDInteger makeFromIndex(
      BDDFactory factory, int length, int start, boolean reverse) {
    return new MutableBDDInteger(factory, bitvector(factory, length, start, reverse));
  }

  /** Create an integer and initialize it to a concrete value */
  public static MutableBDDInteger makeFromValue(BDDFactory factory, int length, long value) {
    MutableBDDInteger bdd = new MutableBDDInteger(factory, length);
    bdd.setValue(value);
    return bdd;
  }

  public static MutableBDDInteger makeMaxValue(BDDFactory factory, int length) {
    MutableBDDInteger bdd = new MutableBDDInteger(factory, length);
    bdd.setValue(bdd._maxVal);
    return bdd;
  }

  /** Set this BDD to have an exact value */
  public void setValue(long val) {
    checkArgument(val >= 0, "Cannot set a negative value");
    checkArgument(val <= _maxVal, "value %s is out of range [0, %s]", val, _maxVal);
    long currentVal = val;
    for (int i = _bitvec.length - 1; i >= 0; i--) {
      if ((currentVal & 1) != 0) {
        _bitvec[i] = _factory.one();
      } else {
        _bitvec[i] = _factory.zero();
      }
      currentVal >>= 1;
    }
  }

  @Override
  public Optional<Long> getValueSatisfying(BDD bdd) {
    return bdd.isZero() ? Optional.empty() : Optional.of(satAssignmentToLong(bdd.satOne()));
  }

  @Override
  public long satAssignmentToLong(BDD satAssignment) {
    checkArgument(satAssignment.isAssignment(), "not a satisfying assignment");
    checkArgument(
        _bitvec.length <= 63, "Only BDDInteger of 63 or fewer bits can be converted to long");

    // we must "complete" the given partial assignment in order to properly get models in the face
    // of mutation, where this object represents a function of the original BDD variables. we could
    // use BDD::fullSatOne to do that, but if there are many BDD variables then that will create a
    // very large BDD, which can cause performance issues. instead we only explicitly treat as false
    // the variables that do not appear in the given SAT assignment but are part of the support of
    // this MutableBDDInteger.
    BDD fullSatAssignment =
        satAssignment.satOne(
            satAssignment
                .getFactory()
                .andAll(Arrays.stream(_bitvec).map(BDD::support).collect(Collectors.toSet())),
            false);

    long value = 0;
    for (int i = 0; i < _bitvec.length; i++) {
      BDD bitBDD = _bitvec[_bitvec.length - i - 1];
      if (fullSatAssignment.andSat(bitBDD)) {
        value |= 1L << i;
      }
    }
    return value;
  }

  /** Check if the first length bits match the BDDInteger representing the advertisement prefix. */
  @Override
  protected BDD firstBitsEqual(long value, int length) {
    checkArgument(length <= _bitvec.length, "Not enough bits");
    long startBDDCount = _factory.numOutstandingBDDs();
    checkState(_trues.isEmpty(), "Unexpected array state");
    checkState(_falses.isEmpty(), "Unexpected array state");
    // 192.168.0.0/16 -> 192.168.0.0 >> 16 -> 192.168
    long val = value >> (_bitvec.length - length);
    for (int i = length - 1; i >= 0; i--) {
      boolean bitValue = (val & 1) == 1;
      if (bitValue) {
        _trues.add(_bitvec[i]);
      } else {
        _falses.add(_bitvec[i]);
      }
      val >>= 1;
    }
    // BDDFactory addAll: Returns the logical 'and' of zero or more BDDs.
    // BDDFactory orAll:  Returns the logical  'or' or zero or more BDDs.
    // BDD diffWith: Makes this BDD to the logical 'difference' of two BDDs, 
    //               which equivalent to BDD this.and(that.not()).
    // scenario 1: _bitvec is 1100,1101, _trues is 1,1111, _falses is 000,
    //             so result is (1&1&1&1&1) & !(0|0|0)
    BDD result = _factory.andAll(_trues).diffWith(_factory.orAll(_falses));
    _trues.clear();
    _falses.clear();
    assertNoLeaks(startBDDCount, 1);
    return result;
  }

  /** Check if the first length bits match the given value (similar to the BDD example). */
  // public BoolExpr firstBitsEqual(long value, int length) throws Z3Exception {
  //   // Create a bit-vector representing the value with the specified length
  //   BitVecExpr valExpr = ctx.mkBV(value, length);

  //   // Create an array to hold the individual bits from the bit-vector
  //   BoolExpr[] bitConditions = new BoolExpr[length];

  //   // Iterate over each bit in the value and compare it with the corresponding bit in the bit-vector
  //   for (int i = 0; i < length; i++) {
  //     // Get the i-th bit from the value bit-vector
  //     BitVecExpr bit = ctx.mkExtract(i, i, valExpr);

  //     // Check if the bit is 1 (true) or 0 (false) and add the corresponding condition
  //     bitConditions[i] = ctx.mkEq(bit, ctx.mkBV(1, 1)); // Bit is 1
  //   }

  //   // Combine all the bit conditions using AND (similar to 'andAll' in BDD)
  //   BoolExpr result = ctx.mkAnd(bitConditions);

  //   return result;
  // }

  @Override
  public BDD toBDD(IpWildcard ipWildcard) {
    // network prefix    192.168.0.0/16
    // network wildcard  192.168.0.0/255.255.0.0
    // '1' in wildcard means the corresponding bit in the ip address is fixed
    // '0' in wildcard means the corresponding bit in the ip address is variable

    // _factory.andAll(aBDD, bBDD, ...): return aBDD & bBDD & ...
    // _factory.orAll(aBDD, bBDD, ...):  return aBDD | bBDD | ...
    // aBDD.diffWith(bBDD):              return aBDD & (!bBDD)
    // scenario 1: 192.168.0.0/255.255.0.0
    //             i.e. 1100_0000.1010_1000.0000_0000.0000_0000/
    //                  1111_1111.1111_1111.0000_0000.0000_0000
    // exact match result = (1&1&1&1) & !(0|0|0|0|0|0|0|0|0|0|0|0)
    checkArgument(_bitvec.length >= Prefix.MAX_PREFIX_LENGTH);
    long startBDDCount = _factory.numOutstandingBDDs();
    long ip = ipWildcard.getIp().asLong();
    long wildcard = ipWildcard.getWildcardMask();
    checkState(_trues.isEmpty(), "Unexpected array state");
    checkState(_falses.isEmpty(), "Unexpected array state");
    for (int i = Prefix.MAX_PREFIX_LENGTH - 1; i >= 0; i--) {
      boolean significant = !Ip.getBitAtPosition(wildcard, i);
      if (significant) {
        boolean bitValue = Ip.getBitAtPosition(ip, i);
        if (bitValue) {
          _trues.add(_bitvec[i]);
        } else {
          _falses.add(_bitvec[i]);
        }
      }
    }
    BDD result = _factory.andAll(_trues).diffWith(_factory.orAll(_falses));
    _trues.clear();
    _falses.clear();
    assertNoLeaks(startBDDCount, 1);
    return result;
  }

  /*
   * Add two BDDs bitwise to create a new BDD
   */
  public MutableBDDInteger add(BDDInteger other) {
    BDD[] as = _bitvec;
    BDD[] bs = other._bitvec;

    checkArgument(as.length > 0, "Cannot add BDDIntegers of length 0");
    checkArgument(as.length == bs.length, "Cannot add BDDIntegers of different length");

    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDInteger sum = new MutableBDDInteger(_factory, as.length);
    BDD carry = _factory.zero();
    BDD[] cs = sum._bitvec;
    for (int i = cs.length - 1; i > 0; --i) {
      cs[i] = as[i].xor(bs[i]).xorEq(carry);
      carry = as[i].and(bs[i]).orWith(as[i].or(bs[i]).andWith(carry));
    }
    cs[0] = carry.xorEq(as[0]).xorEq(bs[0]);
    assertNoLeaks(startBDDCount, _bitvec.length);
    return sum;
  }

  /*
   * Add two BDDs bitwise to create a new BDD. Clips to MAX_VALUE in case of overflow.
   */
  public MutableBDDInteger addClipping(MutableBDDInteger other) {
    BDD[] as = _bitvec;
    BDD[] bs = other._bitvec;

    checkArgument(as.length > 0, "Cannot add BDDIntegers of length 0");
    checkArgument(as.length == bs.length, "Cannot add BDDIntegers of different length");

    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDInteger sum = new MutableBDDInteger(_factory, as.length);
    BDD[] cs = sum._bitvec;
    BDD carry = _factory.zero();
    for (int i = cs.length - 1; i >= 0; --i) {
      cs[i] = as[i].xor(bs[i]).xorEq(carry);
      carry = as[i].and(bs[i]).orWith(carry.andWith(as[i].or(bs[i])));
    }
    MutableBDDInteger maxValue = makeMaxValue(_factory, _bitvec.length);
    MutableBDDInteger result = sum.ite(carry.notEq(), maxValue);
    maxValue.free();
    sum.free();
    carry.free();
    assertNoLeaks(startBDDCount, _bitvec.length);
    return result;
  }

  private void assertNoLeaks(long startBDDs, long incremental) {
    assert _factory.numOutstandingBDDs() == startBDDs + incremental
        : String.format(
            "Expected to create %d new BDDs, actually created %d",
            incremental, _factory.numOutstandingBDDs() - startBDDs);
  }

  /**
   * Free all the component {@link BDD BDDs} in this {@link BDDInteger}. This instance is no longer
   * safe to use unless re-initialized via, e.g., {@link #setValue(long)}.
   */
  public void free() {
    for (int i = 0; i < _bitvec.length; i++) {
      _bitvec[i].free();
      _bitvec[i] = null;
    }
  }

  /*
   * Map an if-then-else over each bit in the bitvector
   */
  public MutableBDDInteger ite(BDD b, MutableBDDInteger other) {
    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDInteger val = new MutableBDDInteger(_factory, _bitvec.length);
    for (int i = 0; i < _bitvec.length; i++) {
      val._bitvec[i] = b.ite(_bitvec[i], other._bitvec[i]);
    }
    assertNoLeaks(startBDDCount, _bitvec.length);
    return val;
  }

  /**
   * @param pred a predicate
   * @return the same bitvector but restricted by pred.
   */
  public MutableBDDInteger and(BDD pred) {
    long startBDDCount = _factory.numOutstandingBDDs();
    MutableBDDInteger val = new MutableBDDInteger(_factory, _bitvec.length);
    for (int i = 0; i < _bitvec.length; i++) {
      val._bitvec[i] = pred.and(_bitvec[i]);
    }
    assertNoLeaks(startBDDCount, _bitvec.length);
    return val;
  }

  /**
   * Produces a BDD whose models represent all possible differences between the two BDDIntegers --
   * valuations of the BDD variables that cause the two BDDIntegers to have different values. The
   * two BDDIntegers are assumed to have the same length.
   *
   * @param other the second BDDInteger
   * @return a predicate represented as a BDD
   */
  public BDD allDifferences(BDDInteger other) {
    long startBDDCount = _factory.numOutstandingBDDs();
    assert _bitvec.length == other._bitvec.length;
    BDD result =
        _factory.orAllAndFree(
            IntStream.range(0, _bitvec.length)
                .mapToObj(i -> _bitvec[i].xor(other._bitvec[i]))
                .collect(ImmutableList.toImmutableList()));
    assertNoLeaks(startBDDCount, 1);
    return result;
  }

  /*
   * Set this BDD to be equal to another BDD
   */
  public void setValue(MutableBDDInteger other) {
    for (int i = 0; i < _bitvec.length; ++i) {
      _bitvec[i] = other._bitvec[i].id();
    }
  }

  /*
   * Subtract one BDD from another bitwise to create a new BDD
   */
  public MutableBDDInteger sub(MutableBDDInteger other) {
    checkArgument(
        _bitvec.length == other._bitvec.length, "Input variable must have equal bitvector length");

    int length = _bitvec.length;
    long startBDDCount = _factory.numOutstandingBDDs();
    BDD[] a = _bitvec;
    BDD[] b = other._bitvec;
    MutableBDDInteger result = new MutableBDDInteger(_factory, length);
    BDD[] c = result._bitvec; // We will compute c = a - b.
    BDD borrow = _factory.zero(); // the opposite of carry
    for (int i = length - 1; i >= 0; --i) {
      c[i] = a[i].xor(b[i]).xorEq(borrow);
      BDD var7 = b[i].or(borrow).diffEq(a[i]);
      borrow = a[i].and(b[i]).andWith(borrow).orWith(var7);
    }
    borrow.free();
    assertNoLeaks(startBDDCount, _bitvec.length);
    return result;
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof MutableBDDInteger)) {
      return false;
    }
    MutableBDDInteger other = (MutableBDDInteger) o;
    // No need to check _factory
    return Arrays.equals(_bitvec, other._bitvec);
  }

  @Override
  public int hashCode() {
    return Arrays.hashCode(_bitvec);
  }
}
