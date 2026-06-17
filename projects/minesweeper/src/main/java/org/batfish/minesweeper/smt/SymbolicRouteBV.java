package org.batfish.minesweeper.smt;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Model;
import java.math.BigInteger;
import java.util.Map;
import java.util.Set;
import javax.annotation.Nullable;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.IDeepCopy;
import org.batfish.minesweeper.Protocol;
import org.batfish.common.BatfishException;

public final class SymbolicRouteBV extends SymbolicRouteBase
    implements IDeepCopy<SymbolicRouteBV> {

  private BitVecExpr _communitiesBitVec;
  private int _width;

  SymbolicRouteBV(String name, Protocol proto) {
    super(name, proto);
    _communitiesBitVec = null;
  }

  SymbolicRouteBV(SymbolicRouteBV other) {
    super(other);
    _communitiesBitVec = other._communitiesBitVec;
  }

  SymbolicRouteBV(
      EncoderSlice slice,
      String name,
      String router,
      Protocol proto,
      Optimizations opts,
      @Nullable SymbolicEnum<Protocol> h,
      boolean isAbstract) {
    super(slice, name, router, proto, opts, h, isAbstract);
  }

  /** Returns {@code route} if it is an instance of this class; otherwise throws. */
  public static SymbolicRouteBV cast(SymbolicRouteBase route) {
    if (route instanceof SymbolicRouteBV) {
      return (SymbolicRouteBV) route;
    }
    throw new IllegalArgumentException("Expected SymbolicRouteBV, got " + route.getClass());
  }

  @Override
  public SymbolicRouteBV copy() {
    return new SymbolicRouteBV(this);
  }

  @Override
  public SymbolicRouteBV deepCopy() {
    return copy();
  }

  @Override
  protected void initCommunities(
      EncoderSlice slice,
      String name,
      String router,
      Protocol proto,
      Optimizations opts,
      Context ctx,
      boolean usesBgp) {
    _communitiesBitVec = null;
    if (usesBgp) {
      _width = slice.getGraph().getAllCommunitiesIndex().size();
      if (0 != _width) {
        _communitiesBitVec = ctx.mkBVConst(name + "_community", _width);
      } else {
        // empty communities
        _communitiesBitVec = null;
      }
    }
  }

  @Override
  protected void addCommunityExprs(Map<String, Expr> all) {
    if (_communitiesBitVec != null) {
      all.put(_communitiesBitVec.toString(), _communitiesBitVec);
    }
  }

  @Override
  public Map<CommunityVar, BoolExpr> getCommunities() {
    throw new UnsupportedOperationException(
        "SymbolicRouteBV uses BitVec encoding; use getCommunitiesBitVec()");
  }

  @Override
  public void setCommunities(Map<CommunityVar, BoolExpr> communities) {
    throw new UnsupportedOperationException(
        "SymbolicRouteBV uses BitVec encoding; use setCommunitiesBitVec(BitVecExpr)");
  }

  @Nullable
  public BitVecExpr getCommunitiesBitVec() {
    return _communitiesBitVec;
  }

  public void setCommunitiesBitVec(@Nullable BitVecExpr communitiesBitVec) {
    _communitiesBitVec = communitiesBitVec;
  }

  public int getWidth() {
    return _width;
  }

  public static BitVecExpr communitiesMask(
      Context ctx, ImmutableMap<CommunityVar, Integer> commsIndex, Iterable<CommunityVar> comms) {
    if (commsIndex.size() > 64) {
      // FIXME: support more than 64 communities in the future
      throw new BatfishException("communitiesMask: out of range for long type: " + commsIndex.size());
    }

    long mask = 0;
    for (CommunityVar comm : comms) {
      Integer index = commsIndex.get(comm);
      if (index == null) {
        throw new BatfishException("communitiesMask: unknown community: " + comm);
      }
      mask |= 1L << index;
    }
    return ctx.mkBV(mask, commsIndex.size());
  }

  public static ImmutableSet<CommunityVar> communitiesVars(
      BitVecNum comm, ImmutableMap<CommunityVar, Integer> commsIndex) {
    if (commsIndex.size() > 64) {
      // FIXME: support more than 64 communities in the future
      throw new BatfishException("communitiesVar: out of range for long type: " + commsIndex.size());
    }

    if (null == comm) {
      return ImmutableSet.of();
    }

    BigInteger commsBit = comm.getBigInteger();
    ImmutableSet.Builder<CommunityVar> commsVars = ImmutableSet.builder();
    for (Map.Entry<CommunityVar, Integer> commIndex : commsIndex.entrySet()) {
      if (commsBit.testBit(commIndex.getValue())) {
        commsVars.add(commIndex.getKey());
      }
    }
    return commsVars.build();
  }

  public static BoolExpr communitiesEmpty(Context ctx, BitVecExpr comms, int width) {
    if (null == comms) {
      return ctx.mkTrue();
    }
    return ctx.mkEq(comms, ctx.mkBV(0, width));
  }

  public static BoolExpr communitiesEqual(Context ctx, BitVecExpr comms1, BitVecExpr comms2) {
    if (null == comms1 && null == comms2) {
      return ctx.mkTrue();
    } else if (null == comms1 || null == comms2) {
      return ctx.mkFalse();
    }
    return ctx.mkEq(comms1, comms2);
  }

  public static BoolExpr communitiesMatch(Context ctx, BitVecExpr commsMatch, int width) {
    if (null == commsMatch) {
      return ctx.mkTrue();
    }
    return ctx.mkNot(communitiesEmpty(ctx, commsMatch, width));
  }
}