package elle;

/* A bitmask-backed set of relationships like {ww, rw}. */

import io.lacuna.bifurcan.ISet;
import io.lacuna.bifurcan.Set;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.function.BinaryOperator;

import clojure.lang.Keyword;
import clojure.lang.PersistentHashSet;

public class BitRels implements Iterable<BitRels> {
  public static BitRels NONE = new BitRels((byte) 0x00);
  public static BitRels WW = new BitRels((byte) 0x01);
  public static BitRels WR = new BitRels((byte) 0x02);
  public static BitRels RW = new BitRels((byte) 0x04);
  public static BitRels WWP = new BitRels((byte) 0x08);
  public static BitRels WRP = new BitRels((byte) 0x10);
  public static BitRels RWP = new BitRels((byte) 0x20);
  public static BitRels PROCESS = new BitRels((byte) 0x40);
  public static BitRels REALTIME = new BitRels((byte) 0x80);

  public static BitRels ANY_RW = RW.union(RWP);

  // IMPORTANT: the ALL array is in exactly the order of ascending set bits.
  public static BitRels[] ALL = { WW, WR, RW, WWP, WRP, RWP, PROCESS, REALTIME };
  // IMPORTANT: These arrays are all in the same order
  public static String[] NAMES = { "ww", "wr", "rw", "wwp", "wrp", "rwp", "process", "realtime" };
  public static Keyword[] KEYWORDS = {
      Keyword.intern("ww"),
      Keyword.intern("wr"),
      Keyword.intern("rw"),
      Keyword.intern("wwp"),
      Keyword.intern("wrp"),
      Keyword.intern("rwp"),
      Keyword.intern("process"),
      Keyword.intern("realtime")
  };

  public static BinaryOperator<BitRels> UNION = (a, b) -> a.union(b);

  public final byte rels;

  /* Performs set union on raw byte representations */
  public static byte rawUnion(byte a, byte b) {
    return (byte) (a | b);
  }

  /* Set difference on raw byte representation */
  public static byte rawDifference(byte a, byte b) {
    return (byte) (a & ~b);
  }

  /* Set intersection on raw byte representation */
  public static byte rawIntersection(byte a, byte b) {
    return (byte) (a & b);
  }

  /* Is the given raw byte representation any kind of RW? */
  public static boolean rawIsAnyRW(final byte rel) {
    return (0 != rawIntersection(rel, ANY_RW.rels));
  }

  public BitRels(final byte rels) {
    this.rels = rels;
  }

  // Is this an empty set?
  public boolean isEmpty() {
    return rels == 0x00;
  }

  // Is this a singleton set?
  public boolean isSingleton() {
    return (Integer.bitCount(rels) == 1);
  }

  // Is this purely a predicate edge, or are there other edges?
  public boolean isPredicate() {
    return !(intersection(WWP.union(WRP).union(RWP)).isEmpty());
  }

  // Is this an RW edge, either a single or predicate?
  public boolean isAnyRW() {
    return !(intersection(ANY_RW).isEmpty());
  }

  public BitRels intersection(final BitRels other) {
    return new BitRels((byte) (rels & other.rels));
  }

  public BitRels intersection(final byte other) {
    return new BitRels((byte) (rels & other));
  }

  public BitRels union(final BitRels other) {
    return new BitRels((byte) (rels | other.rels));
  }

  public BitRels union(final byte other) {
    return new BitRels((byte) (rels | other));
  }

  // Returns a Rels with everything in this rels that is *not* in the other rels.
  public BitRels difference(BitRels other) {
    return new BitRels((byte) (rels & (~other.rels)));
  }

  // Explodes into a collection of singleton BitRels.
  public Iterator<BitRels> iterator() {
    return new BitRelsIterator(this);
  }

  public boolean equals(Object other) {
    if (!(other instanceof BitRels)) {
      return false;
    }
    return (rels == ((BitRels) other).rels);
  }

  public int hashCode() {
    return rels;
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("#{");
    boolean comma = false;
    for (int i = 0; i < ALL.length; i++) {
      if (!intersection(ALL[i]).isEmpty()) {
        if (comma) {
          sb.append(", ");
        } else {
          comma = true;
        }
        sb.append(NAMES[i]);
      }
    }
    sb.append('}');
    return sb.toString();
  }

  public ISet<Keyword> toBifurcan() {
    ISet<Keyword> set = Set.EMPTY.linear();
    for (int i = 0; i < ALL.length; i++) {
      if (!intersection(ALL[i]).isEmpty()) {
        set = set.add(KEYWORDS[i]);
      }
    }
    return set.forked();
  }

  public Object toClojure() {
    final ArrayList<Object> kws = new ArrayList<Object>(ALL.length);
    for (int i = 0; i < ALL.length; i++) {
      if (!intersection(ALL[i]).isEmpty()) {
        kws.add(KEYWORDS[i]);
      }
    }
    return PersistentHashSet.create(kws);
  }

  class BitRelsIterator implements Iterator<BitRels> {
    private byte i = -1; // Index of the current rel in ALL, also index of the bit set.
    private final BitRels rels;

    BitRelsIterator(final BitRels rels) {
      this.rels = rels;
    }

    @Override
    public boolean hasNext() {
      // Taking advantage of the fact that ALL's order is exactly bit order
      // 0xFF << i masks off every bit at or lower than i. Note that Java doesn't have bitwise & on bytes: it implicitly widens both bytes to ints, which would fill in the upper bits of rels.rels with 1s. That's why we do the unsigned int conversion here.
      if ((Byte.toUnsignedInt(rels.rels) & (0xFF << (i + 1))) != 0) {
        return true;
      }
      return false;
    }

    @Override
    public BitRels next() {
      // Increment i until we run out of ALLs
      BitRels r;
      while (i < (ALL.length - 1)) {
        i++;
        r = ALL[i];
        if (!rels.intersection(r).isEmpty()) {
          // We contain this singleton!
          return r;
        }
      }
      // Done
      throw new NoSuchElementException();
    }
  }
}