package elle;

import java.util.Iterator;
import java.util.function.BiPredicate;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.ToLongFunction;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import io.lacuna.bifurcan.DirectedGraph;
import io.lacuna.bifurcan.Graphs;
import io.lacuna.bifurcan.IEdge;
import io.lacuna.bifurcan.IEntry;
import io.lacuna.bifurcan.IGraph;
import io.lacuna.bifurcan.IMap;
import io.lacuna.bifurcan.ISet;
import io.lacuna.bifurcan.List;
import io.lacuna.bifurcan.Map;
import io.lacuna.bifurcan.Set;

/**
 * @author aphyr
 * 
 *         RelGraph represents a graph of jepsen history Operations where edges
 *         are are tagged with BitRels. Gluing together n graphs with different
 *         relationships is quick, as is getting a view of the graph with just
 *         one or two relationships in it.
 * 
 *         We use this extensively in Elle for tracking graphs with e.g. ww, wr,
 *         and rw edges--there are times where we want all three in the same
 *         graph, but then we might want to project to *just* ww edges to find a
 *         particular kind of cycle. We burn a ton of time in this projection,
 *         so it's worth optimizing.
 */

public class RelGraph<V> implements IGraph<V, BitRels>, ElleGraph {
  private static final Object DEFAULT = new Object();
  private static final Set<Object> EMPTY_SET = new Set<Object>();
  private static final Set<Object> SINGLE_NULL_SET = new Set<Object>().add(null);

  private boolean linear;
  private ToLongFunction<V> vertexHash;
  private BiPredicate<V, V> vertexEquality;
  // We store a map of singleton Bitrels to the directed graph for that particular
  // relationship.
  private IMap<BitRels, IGraph<V, Object>> graphs;

  private RelGraph(boolean linear, ToLongFunction<V> vertexHash, BiPredicate<V, V> vertexEquality,
      IMap<BitRels, IGraph<V, Object>> graphs) {

    this.linear = linear;
    this.vertexHash = vertexHash;
    this.vertexEquality = vertexEquality;
    if (linear) {
      this.graphs = graphs.linear();
    } else {
      this.graphs = graphs.forked();
    }
  }

  public RelGraph(ToLongFunction<V> vertexHash, BiPredicate<V, V> vertexEquality) {
    this(false, vertexHash, vertexEquality, new Map<BitRels, IGraph<V, Object>>());
  }

  /*
   * Adds a single graph to this relgraph, using the given relationship. Like
   * graph union merging edges, only O(1).
   */
  public RelGraph<V> union(NamedGraph<V, BitRels> graph) {
    final BitRels rel = graph.name();
    if (graphs.contains(rel)) {
      throw new IllegalArgumentException("Already have relationship " + rel);
    }
    if (!vertexHash.equals(graph.vertexHash())) {
      throw new IllegalArgumentException("All graphs must have same vertex hash");
    }
    if (!vertexEquality.equals(graph.vertexEquality())) {
      throw new IllegalArgumentException("All graphs must have same vertex equality");
    }
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.put(rel, graph.graph());
    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  /* Unions another RelGraph into this one. */
  public RelGraph<V> union(RelGraph<V> graph) {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs;
    for (IEntry<BitRels, IGraph<V, Object>> kv : graph.graphs) {
      final BitRels rel = kv.key();
      assert rel.isSingleton();
      final IGraph<V, Object> g = kv.value();
      if (graphs.contains(rel)) {
        throw new IllegalArgumentException("Already have relationship " + rel);
      }
      if (!vertexHash.equals(g.vertexHash())) {
        throw new IllegalArgumentException("All graphs must have same vertex hash");
      }
      if (!vertexEquality.equals(g.vertexEquality())) {
        throw new IllegalArgumentException("All graphs must have same vertex equality");
      }
      graphsPrime = graphsPrime.put(rel, g);
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    }
    return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
  }

  /* Projects this graph to a single relationship */
  public NamedGraph<V, BitRels> projectRel(BitRels rel) {
    return new NamedGraph<V, BitRels>(rel, graphs.get(rel, new DirectedGraph<V, Object>(vertexHash, vertexEquality)));
  }

  /* Projects this graph to just a specific subset of relationships. */
  public RelGraph<V> projectRels(Iterable<BitRels> rels) {
    // Just copy over those subgraphs
    IMap<BitRels, IGraph<V, Object>> graphsPrime = new Map<BitRels, IGraph<V, Object>>().linear();
    for (BitRels rel : rels) {
      IGraph<V, Object> g = graphs.get(rel, null);
      if (g != null) {
        graphsPrime = graphsPrime.put(rel, g);
      }
    }
    return new RelGraph<V>(linear, vertexHash, vertexEquality, graphsPrime.forked());
  }

  // Materializing the vertex set is expensive, so we have an optimized routine
  // for checking if empty.
  @Override
  public boolean isEmpty() {
    for (IGraph<V, Object> g : graphs.values()) {
      if (0 < g.vertices().size()) {
        return false;
      }
    }
    return true;
  }

  // ??? @Override
  public Set<V> vertices() {
    if (graphs.size() == 0) {
      return (Set<V>) EMPTY_SET;
    }
    Set<V> vs = (Set<V>) EMPTY_SET.linear();
    for (IGraph<V, Object> g : graphs.values()) {
      vs = vs.union(g.vertices());
    }
    return vs.forked();
  }

  // ??? @Override
  public Iterable<IEdge<V, BitRels>> edges() {
    final Stream<IEdge<V, BitRels>> stream = StreamSupport.stream(vertices().spliterator(), false)
        .flatMap(vertex -> {
          // For this vertex, build up a map of out-vertex->rels.
          IMap<V, BitRels> outrels = new Map<V, BitRels>().linear();
          // Go through each rel, and each set of outs *in* that rel...
          for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
            final BitRels rel = kv.key();
            final IGraph<V, Object> g = kv.value();
            // For each outbound node in this particular graph, add a rel to the map
            try {
              for (V out : g.out(vertex)) {
                outrels = outrels.update(out, rels -> {
                  if (rels == null) {
                    return rel;
                  } else {
                    return rels.union(rel);
                  }
                });
              }
            } catch (IllegalArgumentException e) {
              // No such vertex
            }
          }
          return outrels.stream().map(kv -> new Graphs.DirectedEdge<V, BitRels>(kv.value(), vertex, kv.key()));
        });
    return stream::iterator;
  }

  // ??? @Override
  public BitRels edge(V from, V to) {
    BitRels rels = BitRels.NONE;
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      Object edge = kv.value().edge(from, to, BitRels.NONE);
      if (edge != BitRels.NONE) {
        rels = rels.union(kv.key());
      }
    }

    if (rels.isEmpty()) {
      throw new IllegalArgumentException("no such edge");
    }
    return rels;
  }

  public BitRels edge(V from, V to, BitRels notFound) {
    BitRels rels = BitRels.NONE;
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      Object edge = kv.value().edge(from, to, BitRels.NONE);
      if (edge != BitRels.NONE) {
        rels = rels.union(kv.key());
      }
    }

    if (rels.isEmpty()) {
      return notFound;
    }
    return rels;
  }

  public boolean isLinear() {
    return linear;
  }

  public IGraph<V, BitRels> forked() {
    if (isLinear()) {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphs.forked());
    } else {
      return this;
    }
  }

  public IGraph<V, BitRels> linear() {
    if (isLinear()) {
      return this;
    } else {
      return new RelGraph<V>(true, vertexHash, vertexEquality, graphs.linear());
    }
  }

  public ISet<V> in(V vertex) {
    Set<V> s = (Set<V>) EMPTY_SET.linear();
    boolean present = false;
    for (IGraph<V, Object> g : graphs.values()) {
      try {
        s = s.union(g.in(vertex));
        present = true;
      } catch (IllegalArgumentException e) {
        // No vertex
      }
    }
    if (!present) {
      throw new IllegalArgumentException("no such vertex");
    }
    return s.forked();
  }

  public ISet<V> out(V vertex) {
    Set<V> s = (Set<V>) EMPTY_SET.linear();
    boolean present = false;
    for (IGraph<V, Object> g : graphs.values()) {
      // This contains check is expensive and duplicates work in g.out(), but if we
      // call g.out directly it'll throw and that's *also* expensive, ugh.
      if (g.vertices().contains(vertex)) {
        s = s.union(g.out(vertex));
        present = true;
      }
    }

    if (!present) {
      throw new IllegalArgumentException("no such vertex");
    }
    return s.forked();
  }

  // We actually ignore the merge semantics altogether. Every link, for us, is union.
  public IGraph<V, BitRels> link(V from, V to, BitRels edge, BinaryOperator<BitRels> merge) {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.linear();
    if (edge == null) {
      edge = BitRels.NONE;
    }
    // For each relationship, add a link in that graph.
    for (BitRels rel : edge) {
      IGraph<V, Object> g = graphs.get(rel, new DirectedGraph<V, Object>());
      g = g.link(from, to, null);
      graphsPrime = graphsPrime.put(rel, g);
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime.forked());
    }
  }

  public IGraph<V, BitRels> link(V from, V to, BitRels edge) {
    return link(from, to, edge, null);
  }

  public IGraph<V, BitRels> link(V from, V to) {
    return link(from, to, null);
  }

  public IGraph<V, BitRels> unlink(V from, V to) {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.linear();
    // For each graph, unlink
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      final BitRels rel = kv.key();
      IGraph<V, Object> g = kv.value();
      g = g.unlink(from, to);
      graphsPrime = graphsPrime.put(rel, g);
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime.forked());
    }
  }

  public IGraph<V, BitRels> add(V vertex) {
    IGraph<V, Object> graphPrime = graphs.get(null, new DirectedGraph<V, Object>());
    graphPrime = graphPrime.add(vertex);
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.put(null, graphPrime);

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  public IGraph<V, BitRels> remove(V vertex) {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      final BitRels rel = kv.key();
      IGraph<V, Object> g = kv.value();
      graphsPrime = graphsPrime.put(rel, g.remove(vertex));
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  public <U> IGraph<V, U> mapEdges(Function<IEdge<V, BitRels>, U> f) {
    throw new UnsupportedOperationException();
  }

  public IGraph<V, BitRels> select(ISet<V> vertices) {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      graphsPrime = graphsPrime.put(kv.key(), kv.value().select(vertices));
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  public boolean isDirected() {
    return true;
  }

  public ToLongFunction<V> vertexHash() {
    return vertexHash;
  }

  public BiPredicate<V, V> vertexEquality() {
    return vertexEquality;
  }

  public IGraph<V, BitRels> transpose() {
    IMap<BitRels, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<BitRels, IGraph<V, Object>> kv : graphs) {
      graphsPrime = graphsPrime.put(kv.key(), kv.value().transpose());
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (other instanceof RelGraph) {
      return graphs.equals(((RelGraph<V>) other).graphs);
    }
    return false;
  }

  @Override
  public String toString() {
    return graphs.toString();
  }

  @Override
  public int hashCode() {
    return graphs.hashCode();
  }

  public RelGraph<V> clone() {
    if (isLinear()) {
      return new RelGraph<V>(linear, vertexHash, vertexEquality, graphs.clone());
    } else {
      return this;
    }
  }
}
