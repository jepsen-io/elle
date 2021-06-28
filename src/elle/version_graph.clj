(ns elle.version-graph
  "Constructing an inferred *version graph* is an important step in Elle's
  inference of transaction anomalies. In Adya's formalism, a version order is a
  total order over all installed versions of a given object. In Elle, we
  generalize to all committed (or potentially committed) versions, and we relax
  the order to a graph of relationships, inferred using various techniques.

  If the version graph is cyclic, we know a contradiction exists on a single
  key. For instance, imagine the following history on a single register:

    T1: r1
    T2: w2
    T3: r1

  If T1 < T2 < T3 in real time, we have a *linearizability* violation. Or
  consider:

    T1: r1
    T2: r2
    T3: r2
    T4: r1

  If one process performs T1, T2, and a process performs T3, T4, then (assuming
  unique writes) we have a *sequential* violation.

  So, we can use cycles in the version graph to identify anomalies in a single
  object. If the version graph is *acyclic*, we can use it to inform a
  *transaction* graph.

  That transaction graph, can, in turn, expand the version graph.")

(set! *warn-on-reflection* true)

(defprotocol VersionGraph
  "This protocol identifies the relationships between versions, and can justify
  those relationships."
  (all-keys [_]
            "Returns the set of all keys in this history.")

  (graph [_ k]
         "Returns the Bifurcan directed graph over versions for the given key.")

  (explain-version-pair [_ k v v']
                        "Explains why for key k, version v precedes v'."))
