theory DSG
  imports Main History
begin

section \<open>Transaction Dependencies\<close>

text \<open>We begin by formalizing three types of dependencies between transactions: wr-depends,
ww-depends, and rw-depends. The wr-depends relation captures the idea of a transaction t2 reading
another transaction T1's write.\<close>

definition wr_depends :: "history \<Rightarrow> atxn \<Rightarrow> atxn \<Rightarrow> bool" where
"wr_depends h t1 t2 \<equiv> \<exists>w1 r2. (a_is_committed t1) \<and>
                              (a_is_committed t2) \<and>
                              (w1 \<in> ext_awrites t1) \<and>
                              (r2 \<in> ext_areads t2) \<and>
                              ((key w1) = (key r2)) \<and>
                              ((post_version w1) = (pre_version r2))"

text \<open>We say t1 ww-depends t2 if t2 overwrote t1--that is, if t1 installed
some version v1 of k, and t2 wrote v2, such that v1 came immediately before v2 in the version order
of k.\<close>

definition ww_depends :: "history \<Rightarrow> atxn \<Rightarrow> atxn \<Rightarrow> bool" where
"ww_depends h t1 t2 \<equiv> \<exists>w1 w2.
  (a_is_committed t1) \<and>
  (a_is_committed t2) \<and>
  (w1 \<in> ext_awrites t1) \<and>
  (w2 \<in> ext_awrites t2) \<and>
  ((key w1) = (key w2)) \<and>
  (is_next_in_history h (key w1) (apost_version w1) (apost_version w2))"

lemma ww_depends_example: "ww_depends 
  (History objs
           {(ATxn [(AWrite x v0 a1 v1 [])] True),
            (ATxn [(AWrite x v1 a2 v2 [])] True)}
           {(KeyVersionOrder x [v0, v1, v2])})
  (ATxn [(AWrite x v0 a1 v1 [])] True)
  (ATxn [(AWrite x v1 a2 v2 [])] True)
= True"
  apply (simp add:ww_depends_def)
  done

text \<open>An rw-dependency is just like a ww-dependency, only transaction t1 *read* state just prior to
t2's write.\<close>

definition rw_depends :: "history \<Rightarrow> atxn \<Rightarrow> atxn \<Rightarrow> bool" where
"rw_depends h t1 t2 \<equiv> \<exists>r1 w2.
  (a_is_committed t1) \<and>
  (a_is_committed t2) \<and>
  (r1 \<in> ext_areads t1) \<and>
  (w2 \<in> ext_awrites t2) \<and>
  ((key r1) = (key w2)) \<and>
  (is_next_in_history h (key r1) (apost_version r1) (apost_version w2))"

section \<open>Direct Serialization Graphs\<close>

text \<open>Now, we define a Direct Serialization Graph of a history as a graph where nodes are
transactions in that history, and arcs are dependencies between them. We codify these three types of
dependency with a type, and create a dependency type to wrap them. We call these aDeps for abstract
dependencies; later, we'll define analogous observed dependencies.\<close>

datatype depType = WR | WW | RW

datatype adep = ADep atxn depType atxn

primrec adep_head :: "adep \<Rightarrow> atxn" where
"adep_head (ADep t _ _) = t"

primrec adep_tail :: "adep \<Rightarrow> atxn" where
"adep_tail (ADep _ _ t) = t"

class dep_typed =
  fixes dep_type :: "'a \<Rightarrow> depType"

instantiation adep :: "dep_typed"
begin
primrec dep_type_adep :: "adep \<Rightarrow> depType" where
"dep_type_adep (ADep _ t _) = t"
instance ..
end

type_synonym dsg = "(atxn, adep) pre_digraph"

text \<open>The DSG of a history is defined by mapping each dependency to an edge in the graph.\<close>

definition dsg :: "history \<Rightarrow> dsg" where
"dsg h \<equiv> \<lparr>verts = all_atxns h,
          arcs  = ({(ADep t1 WR t2) | t1 t2. wr_depends h t1 t2} \<union>
                   {(ADep t1 WW t2) | t1 t2. ww_depends h t1 t2} \<union>
                   {(ADep t1 RW t2) | t1 t2. rw_depends h t1 t2}),
          tail = adep_tail,
          head = adep_head\<rparr>"


text \<open>Now, we need to characterize a cycle in a DSG. TODO: I don't know how to use the definitions
in the locales in Arc_Walk.thy, but I assume we should take advantage of them. Copy-pasting with
slight mods for now.\<close>

type_synonym 'a path = "'a list"

text \<open>The list of vertices of a walk. The additional vertex argument is there to deal with the case
of empty walks.\<close>

primrec path_verts :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b path \<Rightarrow> 'a list" where
    "path_verts G u [] = [u]"
  | "path_verts G u (e # es) = tail G e # path_verts G (head G e) es"

text \<open>
  Tests whether a list of arcs is a consistent arc sequence,
  i.e. a list of arcs, where the head G node of each arc is
  the tail G node of the following arc.
\<close>
fun cas :: "('a, 'b) pre_digraph => 'a \<Rightarrow> 'b path \<Rightarrow> 'a \<Rightarrow> bool" where
  "cas G u [] v = (u = v)" |
  "cas G u (e # es) v = (tail G e = u \<and> cas G (head G e) es v)"

definition path :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b path \<Rightarrow> 'a \<Rightarrow> bool" where
  "path G u p v \<equiv> u \<in> verts G \<and> set p \<subseteq> arcs G \<and> cas G u p v"

text \<open>Is the given path a cycle in the given graph?\<close>

definition cycle :: "('a,'b) pre_digraph \<Rightarrow> 'b path \<Rightarrow> bool" where
  "cycle G p \<equiv> \<exists>u. path G u p u \<and> distinct (tl (path_verts G u p)) \<and> p \<noteq> []"

text \<open>We would like a cycle whose edges are all of the given set of dependency types.\<close>

primrec path_dep_types :: "('a::dep_typed) path \<Rightarrow> depType set" where
"path_dep_types []        = {}" |
"path_dep_types (x # xs)  = (Set.insert (dep_type x) (path_dep_types xs))"

end