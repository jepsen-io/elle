package elle;

import io.lacuna.bifurcan.IList;

/* A specialized representation of a path taken during BFS search through a transaction graph. See elle.bfs. 
 */

import io.lacuna.bifurcan.ISet;
import io.lacuna.bifurcan.IntSet;
import io.lacuna.bifurcan.LinearList;
import io.lacuna.bifurcan.List;
import io.lacuna.bifurcan.Set;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.function.BinaryOperator;

import javax.swing.border.EmptyBorder;

import clojure.lang.Keyword;
import clojure.lang.PersistentHashSet;

public class BFSPath {
  // Mode for RW edges. NONE means take RW edges iff legal. SINGLE means take
  // exactly one RW edge, then flip to NONE. NONADJACENT_FREE and
  // NONADJACENT_TAKEN flip back and forth to find G-nonadjacent.
  public enum RWMode {
    NONE, SINGLE, NONADJACENT_FREE, NONADJACENT_TAKEN
  }

  // Takes a set of up to four BitRels and packs it into an integer.
  public static int packRelsSet(final ISet<BitRels> relsSet) {
    assert relsSet.size() <= 4;
    int i = 0;
    int packed = 0;
    for (final BitRels rels : relsSet) {
      packed = packed | (Byte.toUnsignedInt(rels.rels) << i);
      i += 8;
    }
    return packed;
  }

  // Unpacks a set of BitRels from an integer.
  public static ISet<BitRels> unpackRelsSet(final int relsSet) {
    ISet<BitRels> set = Set.EMPTY;
    BitRels rels;
    for (byte i = 0; i < 32; i += 8) {
      rels = new BitRels((byte) (relsSet >>> i));
      if (! rels.isEmpty()) {
        set = set.add(rels);
      }
    }
    return set;
  }

  // Takes a packed set of BitRels and collapses it into a single mask which will intersect with any BitRels that intersects with any element of the set
  public static byte packedSetToMask(int rels) {
    // We shift rels over one byte at a time, unioning with itself.
    for (byte i = 0; i < 32; i += 8) {
      rels = rels | rels >>> i;
    }
    // This means the lower byte is now the mask we want.
    return (byte) rels;
  }

  // Takes a set of (up to) four wanted BitRels packed into an int, and a BitRels rel we're taking. Returns the wanted set with up to one of the four BitRels zeroed out iff the given rel intersects with it.
  public static int checkOffRelInPackedSet(final int rels, final byte rel) {
    // Loop through bytes
    int mask;
    byte thisRel;
    for (byte i = 0; i < 32; i += 8) {
      mask = 0xFF << i;
      thisRel = (byte) ((rels & mask) >>> i);
      if (0 != BitRels.rawIntersection(thisRel, rel)) {
        // Our rel intersects this rel. Zero it out.
        return rels & (~mask);
      }
    }
    return rels;
  }

  // BitRels representation of the edges we can normally take
  public final byte legal;
  // Up to four BitRels packed into an int, representing the rels we still want to take. This number needs to be zero for a path to be valid. We can zero out any single bitrels set in this structure by taking a rel that intersects that set.
  public final int want;
  // Number of RW edges we're waiting to take: 0, 1, or 2
  public final byte wantRW;
  // What kind of RW traversal we're doing
  public final RWMode rwMode;
  // What's the index of the last op we visited?
  public final long lastIndex;
  // The set of indices we've visited
  public final IntSet indexSet;
  // The list of ops we visited, in order
  public final IList<Object> ops;

  public BFSPath(final byte legal, final int want, final byte wantRW, final RWMode rwMode, final long lastIndex,
      final IntSet indexSet, final IList<Object> ops) {
    this.legal = legal;
    this.want = want;
    this.wantRW = wantRW;
    this.rwMode = rwMode;
    this.lastIndex = lastIndex;
    this.indexSet = indexSet;
    this.ops = ops;
  }

  public BFSPath(final byte legal, final ISet<BitRels> want, final byte wantRW, final RWMode rwMode) {
    this(legal, packRelsSet(want), wantRW, rwMode, -1L, new IntSet(), (IList<Object>) List.EMPTY);
    assert rwMode != null;
  }

  // A path is valid when the wanted edge bitset is 0, we want no more rws,
  // and our nonadjacent mode is not nonadjacent-taken (since we always start
  // with an rw edge for nonadjacent paths)
  public boolean isValid() {
    return ((0 == want) &&
        (0 == wantRW) &&
        (!(rwMode == RWMode.NONADJACENT_TAKEN)));
  }

  // A path forms a loop when its last index has been visited before.
  public boolean isLoop() {
    return indexSet.contains(lastIndex);
  }

  // Starts a path off on a single op. We take index and op separately to avoid
  // having to refer to the Op class.
  public BFSPath start(final long index, final Object op) {
    return new BFSPath(legal, want, wantRW, rwMode, index, indexSet, ops.addLast(op));
  }

  // Takes a single step between to the given op using the given singleton rel.
  private BFSPath stepRel(final byte rel, final long index, final Object op) {
    // System.out.println("StepRel " + new BitRels(rel) + " legal " + new BitRels(legal) + " RW mode " + rwMode);
    // assert (new BitRels(rel).isSingleton());
    final boolean isRw = BitRels.rawIsAnyRW(rel);
    // We can simply take this rel; it's legal
    if (0 != BitRels.rawIntersection(rel, legal)) {
      // System.out.println("Legal step");
      // Keep track of how many RWs we want
      final byte wantRW;
      if (isRw) {
        if (0 == this.wantRW) {
          wantRW = 0;
        } else {
          wantRW = (byte) (this.wantRW - 1);
        }
      } else {
        wantRW = this.wantRW;
      }
      // The only case where RW is legal is if RWMode is nil. Any of these implies we
      // did not take an RW edge.
      RWMode rwMode = RWMode.NONE;
      switch (this.rwMode) {
        case NONE:
          rwMode = RWMode.NONE;
          break;
        case SINGLE:
          rwMode = RWMode.SINGLE;
          break;
        case NONADJACENT_FREE:
          rwMode = RWMode.NONADJACENT_FREE;
          break;
        case NONADJACENT_TAKEN:
          rwMode = RWMode.NONADJACENT_FREE;
          break;
      }
      return new BFSPath(legal, checkOffRelInPackedSet(want, rel), wantRW, rwMode, index, indexSet.add(lastIndex),
          ops.addLast(op));
    } else if (isRw) {
      // System.out.println("RW step");
      // So the rel wasn't normally legal, but RWs are special
      switch (this.rwMode) {
        // No more RWs possible
        case NONE:
          return null;
        // We can do exactly one RW
        case SINGLE:
          return new BFSPath(legal, checkOffRelInPackedSet(want, rel), (byte) 0, RWMode.NONE, index,
              indexSet.add(lastIndex),
              ops.addLast(op));
        // We can take a nonadjacent RW
        case NONADJACENT_FREE:
          final byte wantRW;
          if (0 == this.wantRW) {
            wantRW = 0;
          } else {
            wantRW = (byte) (this.wantRW - 1);
          }
          return new BFSPath(legal, checkOffRelInPackedSet(want, rel), wantRW, RWMode.NONADJACENT_TAKEN, index,
              indexSet.add(lastIndex), ops.addLast(op));
        // Can't take two RWs in a row (unless legal)
        case NONADJACENT_TAKEN:
          return null;
      }
    }
    return null;
  }

  // Extends a path to an adjacent op along the given set of rels, returning a
  // list of paths.
  public IList<BFSPath> step(final BitRels edge, final long index, final Object op) {
    final byte rels = edge.rels;
    // There are basically three classes of rel we can take here. One is an RW,
    // which is special. Another is wanted edges. A third is the legal edges. Legal
    // edges are degenerate--they don't result in any difference as far as path
    // state goes, so we need only take one of them. We compute masks for these
    // three different classes of rels.
    //
    // First, is an RW of interest?
    final byte rwMask;
    // If we want RWs, or have a single or free RW Mode, then we can take an RW.
    if ((0 < wantRW) || (rwMode == RWMode.SINGLE) || (rwMode == RWMode.NONADJACENT_FREE)) {
      rwMask = BitRels.ANY_RW.rels;
    } else {
      rwMask = BitRels.NONE.rels;
    }

    // Now, what rels do we want to take eventually?
    final byte wantMask = BitRels.rawDifference(packedSetToMask(want), rwMask);

    // And what rels are otherwise legal?
    final byte legalMask = BitRels.rawDifference(BitRels.rawDifference(legal, rwMask), wantMask);

    // Our output paths
    IList<BFSPath> paths = new LinearList<BFSPath>();
    BFSPath path;
    int i;
    byte rel;

    // With our masks prepared, we can start taking steps. First, RW.
    final byte rwRels = BitRels.rawIntersection(rels, rwMask);
    if (0 != rwRels) {
      // System.out.println("Considering RW rels");
      for (i = 0; i < BitRels.ALL.length; i++) {
        rel = BitRels.rawIntersection(rwRels, (byte) (1 << i));
        if (0 != rel) {
          path = stepRel(rel, index, op);
          if (path != null) {
            paths = paths.addLast(path);
          }
        }
      }
    }

    // Performance optimization: if we want an RW, that's *all* we're willing to
    // take for the first step. We're done here.
    if (0 < wantRW && 1 == ops.size()) {
      return paths;
    }

    // What about a wanted rel?
    final byte wantRels = BitRels.rawIntersection(rels, wantMask);
    if (0 != wantRels) {
      // System.out.println("Considering want rels");
      for (i = 0; i < BitRels.ALL.length; i++) {
        rel = BitRels.rawIntersection(wantRels, (byte) (1 << i));
        if (0 != rel) {
          path = stepRel(rel, index, op);
          if (null != path) {
            paths = paths.addLast(path);
          }
        }
      }
    }

    // Performance optimization, part II: on our first step, we only care about
    // taking RW or wanted rels.
    if (0 != want && 1 == ops.size()) {
      return paths;
    }

    // Finally, we can take legal rels. It doesn't matter which.
    final byte legalRels = BitRels.rawIntersection(rels, legalMask);
    if (0 != legalRels) {
      // System.out.println("Considering legal rels");
      for (i = 0; i < BitRels.ALL.length; i++) {
        rel = BitRels.rawIntersection(legalRels, (byte) (1 << i));
        if (0 != rel) {
          path = stepRel(rel, index, op);
          if (null != path) {
            paths = paths.addLast(path);
            // No point in trying any other rels here; they'd all give equivalent paths.
            return paths;
          }
        }
      }
    }
    return paths;
  }

  public boolean equals(Object other) {
    if (other instanceof BFSPath) {
      final BFSPath o = (BFSPath) other;
      if (legal == o.legal
          && want == o.want
          && wantRW == o.wantRW
          && rwMode == o.rwMode
          && lastIndex == o.lastIndex
          && indexSet == o.indexSet
          && ops == o.ops) {
        return true;
      }
    }
    return false;
  }

  public String toString() {
    return "(Path :legal " + new BitRels(legal)
        + " :want " + unpackRelsSet(want)
        + " :want-rw " + wantRW
        + " :rw-mode " + rwMode
        + " :last-index " + lastIndex
        + " :indexes " + indexSet
        + " :ops " + ops;
  }
}