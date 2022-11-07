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
import io.lacuna.bifurcan.Map;
import io.lacuna.bifurcan.Set;

/**
 * @author aphyr
 * 
 *         RelGraph represents a graph of jepsen history Operations where edges
 *         are are tagged with a set of *relationship* objects. Gluing together
 *         n graphs with different relationships is quick, as is getting a view
 *         of the graph with just one or two relationships in it.
 * 
 *         We use this extensively in Elle for tracking graphs with e.g. ww, wr,
 *         and rw edges--there are times where we want all three in the same
 *         graph, but then we might want to project to *just* ww edges to find a
 *         particular kind of cycle. We burn a ton of time in this projection,
 *         so it's worth optimizing.
 */

public class RelGraph<V, R> implements IGraph<V, Set<R>>, ElleGraph {
  private static final Object DEFAULT = new Object();
  private static final Set<Object> EMPTY_SET = new Set<Object>();

  // Special identity object for union
  public static final RelGraph<Object, Object> EMPTY = new RelGraph<Object, Object>(false, null, null,
      new Map<Object, IGraph<Object, Object>>());

  private boolean linear;
  private ToLongFunction<V> vertexHash;
  private BiPredicate<V, V> vertexEquality;
  // We store a map of relationships to the directed graph for that particular
  // relationship.
  private IMap<R, IGraph<V, Object>> graphs;

  private RelGraph(boolean linear, ToLongFunction<V> vertexHash, BiPredicate<V, V> vertexEquality,
      IMap<R, IGraph<V, Object>> graphs) {
    this.linear = linear;
    this.vertexHash = vertexHash;
    this.vertexEquality = vertexEquality;
    if (linear) {
      this.graphs = graphs.linear();
    } else {
      this.graphs = graphs.forked();
    }
  }

  /*
   * Adds a single graph to this relgraph, using the given relationship. Like
   * graph union merging edges, only O(1).
   */
  public RelGraph<V, R> union(NamedGraph<V, R> graph) {
    final R rel = graph.name();
    if (graphs.contains(rel)) {
      throw new IllegalArgumentException("Already have relationship " + rel);
    }
    if ((vertexHash != null) && !vertexHash.equals(graph.vertexHash())) {
      throw new IllegalArgumentException("All graphs must have same vertex hash");
    }
    if ((vertexEquality != null) && !vertexEquality.equals(graph.vertexEquality())) {
      throw new IllegalArgumentException("All graphs must have same vertex equality");
    }
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.put(rel, graph.graph());
    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, graph.vertexHash(), graph.vertexEquality(), graphsPrime);
    }
  }

  /* Unions another RelGraph into this one. */
  public RelGraph<V, R> union(RelGraph<V, R> graph) {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs;
    ToLongFunction<V> vertexHashPrime = vertexHash;
    BiPredicate<V, V> vertexEqualityPrime = vertexEquality;
    for (IEntry<R, IGraph<V, Object>> kv : graph.graphs) {
      final R rel = kv.key();
      final IGraph<V, Object> g = kv.value();
      if (graphs.contains(rel)) {
        throw new IllegalArgumentException("Already have relationship " + rel);
      }
      if ((vertexHashPrime != null) && !vertexHashPrime.equals(g.vertexHash())) {
        throw new IllegalArgumentException("All graphs must have same vertex hash");
      }
      if ((vertexEqualityPrime != null) && !vertexEqualityPrime.equals(g.vertexEquality())) {
        throw new IllegalArgumentException("All graphs must have same vertex equality");
      }
      graphsPrime = graphsPrime.put(rel, g);
      vertexHashPrime = g.vertexHash();
      vertexEqualityPrime = g.vertexEquality();
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    }
    return new RelGraph<V, R>(false, vertexHashPrime, vertexEqualityPrime, graphsPrime);
  }

  /* Projects this graph to a single relationship */
  public NamedGraph<V, R> projectRel(R rel) {
    return new NamedGraph<V, R>(rel, graphs.get(rel, new DirectedGraph<V, Object>()));
  }

  /* Projects this graph to just a specific subset of relationships. */
  public RelGraph<V, R> projectRels(Iterable<R> rels) {
    // Just copy over those subgraphs
    IMap<R, IGraph<V, Object>> graphsPrime = new Map<R, IGraph<V, Object>>().linear();
    for (R rel : rels) {
      IGraph<V, Object> g = graphs.get(rel, null);
      if (g != null) {
        graphsPrime = graphsPrime.put(rel, g);
      }
    }
    return new RelGraph<V, R>(linear, vertexHash, vertexEquality, graphsPrime.forked());
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
  public Iterable<IEdge<V, Set<R>>> edges() {
    final Stream<IEdge<V, Set<R>>> stream = StreamSupport.stream(vertices().spliterator(), false).flatMap(vertex -> {
      // For this vertex, build up a map of out-vertex->rels.
      IMap<V, Set<R>> outrels = new Map<V, Set<R>>().linear();
      // Go through each rel, and each set of outs *in* that rel...
      for (IEntry<R, IGraph<V, Object>> kv : graphs) {
        final R rel = kv.key();
        final IGraph<V, Object> g = kv.value();
        // For each outbound node in this particular graph, add a rel to the map
        try {
          for (V out : g.out(vertex)) {
            outrels = outrels.update(out, rels -> {
              if (rels == null) {
                return Set.of(rel);
              } else {
                return rels.add(rel);
              }
            });
          }
        } catch (IllegalArgumentException e) {
          // No such vertex
        }
      }
      return outrels.stream().map(kv -> new Graphs.DirectedEdge<V, Set<R>>(kv.value(), vertex, kv.key()));
    });
    return stream::iterator;
  }

  // ??? @Override
  public Set<R> edge(V from, V to) {
    Set<R> rels = (Set<R>) EMPTY_SET.linear();
    for (IEntry<R, IGraph<V, Object>> kv : graphs) {
      try {
        kv.value().edge(from, to); // Explodes if absent
        rels = rels.add(kv.key());
      } catch (IllegalArgumentException e) {
        // No such edge
      }
    }

    if (rels.size() == 0) {
      throw new IllegalArgumentException("no such edge");
    }
    return rels.forked();
  }

  public boolean isLinear() {
    return linear;
  }

  public IGraph<V, Set<R>> forked() {
    if (isLinear()) {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphs.forked());
    } else {
      return this;
    }
  }

  public IGraph<V, Set<R>> linear() {
    if (isLinear()) {
      return this;
    } else {
      return new RelGraph<V, R>(true, vertexHash, vertexEquality, graphs.linear());
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
      // This contains check is expensive and duplicates work in g.out(), but if we call g.out directly it'll throw and that's *also* expensive, ugh.
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

  public IGraph<V, Set<R>> link(V from, V to, Set<R> edge, BinaryOperator<Set<R>> merge) {
    throw new UnsupportedOperationException();
  }

  public IGraph<V, Set<R>> link(V from, V to, Set<R> edge) {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.linear();
    // For each relationship, add a link in that edge.
    for (R rel : edge) {
      IGraph<V, Object> g = graphs.get(rel, new DirectedGraph<V, Object>());
      g = g.link(from, to, null);
      graphsPrime = graphsPrime.put(rel, g);
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime.forked());
    }
  }

  public IGraph<V, Set<R>> link(V from, V to) {
    return link(from, to, null);
  }

  public IGraph<V, Set<R>> unlink(V from, V to) {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.linear();
    // For each graph, unlink
    for (IEntry<R, IGraph<V, Object>> kv : graphs) {
      final R rel = kv.key();
      IGraph<V, Object> g = kv.value();
      g = g.unlink(from, to);
      graphsPrime = graphsPrime.put(rel, g);
    }

    if (isLinear()) {
      this.graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime.forked());
    }
  }

  public IGraph<V, Set<R>> add(V vertex) {
    IGraph<V, Object> graphPrime = graphs.get(null, new DirectedGraph<V, Object>());
    graphPrime = graphPrime.add(vertex);
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.put(null, graphPrime);

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  public IGraph<V, Set<R>> remove(V vertex) {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<R, IGraph<V, Object>> kv : graphs) {
      final R rel = kv.key();
      IGraph<V, Object> g = kv.value();
      graphsPrime = graphsPrime.put(rel, g.remove(vertex));
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  public <U> IGraph<V, U> mapEdges(Function<IEdge<V, Set<R>>, U> f) {
    throw new UnsupportedOperationException();
  }

  public IGraph<V, Set<R>> select(ISet<V> vertices) {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<R, IGraph<V, Object>> kv : graphs) {
      graphsPrime = graphsPrime.put(kv.key(), kv.value().select(vertices));
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime);
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

  public IGraph<V, Set<R>> transpose() {
    IMap<R, IGraph<V, Object>> graphsPrime = graphs.linear();
    for (IEntry<R, IGraph<V, Object>> kv : graphs) {
      graphsPrime = graphsPrime.put(kv.key(), kv.value().transpose());
    }

    if (isLinear()) {
      graphs = graphsPrime;
      return this;
    } else {
      return new RelGraph<V, R>(false, vertexHash, vertexEquality, graphsPrime);
    }
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (other instanceof RelGraph) {
      return graphs.equals(((RelGraph<V, R>) other).graphs);
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

  public RelGraph<V, R> clone() {
    if (isLinear()) {
      return new RelGraph<V, R>(linear, vertexHash, vertexEquality, graphs.clone());
    } else {
      return this;
    }
  }
}
