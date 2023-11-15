package elle;

import java.util.function.BiPredicate;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.ToLongFunction;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import io.lacuna.bifurcan.Graphs;
import io.lacuna.bifurcan.IEdge;
import io.lacuna.bifurcan.IGraph;
import io.lacuna.bifurcan.ISet;
import io.lacuna.bifurcan.Set;

/**
 * @author aphyr
 * 
 *         A graph which has a name associated with it--for instance, :ww or
 *         :wr, for write-write and write-read dependencies. This name is used
 *         for the value of all edges. We use this in conjunction with RelGraph
 *         to combine and split graphs efficiently, rather than storing the
 *         relationships in the edges themselves.
 */

public class NamedGraph<V, N> implements IGraph<V, N>, ElleGraph {
  private static final Set<Object> EMPTY_SET = new Set<Object>();
  private static final Object DEFAULT = new Object();
  private final N name;
  private IGraph<V, Object> graph;

  // Constructs a new RelGraph. Takes a name and a graph. The graph's edges are
  // ignored. All edges in this graph have the same value: `name`.
  public NamedGraph(N name, IGraph<V, Object> graph) {
    this.name = name;
    this.graph = graph;
  }

  public N name() {
    return name;
  }

  public IGraph<V, Object> graph() {
    return graph;
  }

  // Union with a different namedgraph. Both graphs must have the same name.
  public NamedGraph<V, N> union(NamedGraph<V, N> g) {
    if (! name.equals(g.name())) {
      throw new IllegalArgumentException("names differ! " + name + " is not " + g.name());
    }
    IGraph<V, Object> graphPrime = graph.merge(g.graph());
    if (isLinear()) {
      this.graph = graphPrime;
      return this;
    } else {
      return new NamedGraph<V, N>(name, graphPrime);
    }
  }

  @Override
  public boolean isEmpty() {
    return (graph.vertices().size() == 0);
  }

  public NamedGraph<V, N> linear() {
    if (isLinear()) {
      return this;
    } else {
      return new NamedGraph<V, N>(name, graph.linear());
    }
  }

  public boolean isLinear() {
    return graph.isLinear();
  }

  public IGraph<V, N> forked() {
    if (isLinear()) {
      return new NamedGraph<V, N>(name, graph.forked());
    }
    return this;
  }

  public ISet<V> vertices() {
    return graph.vertices();
  }

  public Iterable<IEdge<V, N>> edges() {
    Stream<IEdge<V, N>> stream = StreamSupport.stream(graph.edges().spliterator(), false).map(edge -> {
      return new Graphs.DirectedEdge<V, N>(name, edge.from(), edge.to());
    });
    return stream::iterator;
  }

  public N edge(V from, V to) {
    graph.edge(from, to); // Throws if not present
    return name;
  }

  public N edge(V from, V to, N notFound) {
    Object r = graph.edge(from, to, DEFAULT);
    if (r == DEFAULT) {
      return notFound;
    } else {
      return name;
    }
  }

  public ISet<V> in(V vertex) {
    return graph.in(vertex);
  }

  public ISet<V> out(V vertex) {
    return graph.out(vertex);
  }

  public NamedGraph<V, N> link(V from, V to, N edge, BinaryOperator<N> merge) {
    if (edge.equals(name)) {
      return link(from, to);
    }
    throw new UnsupportedOperationException("Edge must be" + name);
  }

  public NamedGraph<V, N> link(V from, V to, N edge) {
    if (edge.equals(name)) {
      return link(from, to);
    }
    throw new UnsupportedOperationException("Edge must be" + name);
  }

  public NamedGraph<V, N> link(V from, V to) {
    final IGraph<V, Object> graphPrime = graph.link(from, to);
    if (isLinear()) {
      graph = graphPrime;
      return this;
    }
    return new NamedGraph<V, N>(name, graphPrime);
  }

  public NamedGraph<V, N> unlink(V from, V to) {
    final IGraph<V, Object> graphPrime = graph.unlink(from, to);
    if (isLinear()) {
      graph = graphPrime;
      return this;
    }
    return new NamedGraph<V, N>(name, graphPrime);
  }

  public NamedGraph<V, N> add(V vertex) {
    final IGraph<V, Object> graphPrime = graph.add(vertex);
    if (isLinear()) {
      graph = graphPrime;
      return this;
    }
    return new NamedGraph<V, N>(name, graphPrime);
  }

  public NamedGraph<V, N> remove(V vertex) {
    final IGraph<V, Object> graphPrime = graph.remove(vertex);
    if (isLinear()) {
      graph = graphPrime;
      return this;
    }
    return new NamedGraph<V, N>(name, graphPrime);
  }

  public <U> IGraph<V, U> mapEdges(final Function<IEdge<V, N>, U> f) {
    return graph.mapEdges(edge -> {
      return f.apply(new Graphs.DirectedEdge<V,N>(name, edge.from(), edge.to()));
    });
  }

  public NamedGraph<V, N> select(ISet<V> vertices) {
    return new NamedGraph<V,N>(name, graph.select(vertices));
  }

  public boolean isDirected() {
    return graph.isDirected();
  }

  public ToLongFunction<V> vertexHash() {
    return graph.vertexHash();
  }

  public BiPredicate<V, V> vertexEquality() {
    return graph.vertexEquality();
  }

  public NamedGraph<V, N> transpose() {
    return new NamedGraph<V,N>(name, graph.transpose());
  }

  public int hashCode() {
    return graph.hashCode();
  }

  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (other instanceof NamedGraph<?, ?>) {
      return (name.equals(((NamedGraph<V,N>) other).name) &&
      graph.equals(((NamedGraph<V,N>) other).graph()));
    }
    return false;
  }

  public NamedGraph<V, N> clone() {
    if (isLinear()) {
      return new NamedGraph<V,N>(name, graph.clone());
    }
    return this;
  }

  public String toString() {
    return "(NamedGraph " + name + ": " + graph.toString() + ")";
  }
}
