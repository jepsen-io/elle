(* Title:  Digraph_Component_Vwalk.thy
   Author: Lars Noschinski, TU München
*)

theory Digraph_Component_Vwalk
imports
  Digraph_Component
  Vertex_Walk
begin

section \<open>Lemmas for Vertex Walks\<close>

lemma vwalkI_subgraph:
  assumes "vwalk p H"
  assumes "subgraph H G"
  shows "vwalk p G"
proof
  show "set p \<subseteq> verts G" and "p \<noteq> []"
    using assms by (auto simp add: subgraph_def vwalk_def)

  have "set (vwalk_arcs p) \<subseteq> arcs_ends H"
    using assms by (simp add: vwalk_def)
  also have "\<dots> \<subseteq> arcs_ends G"
    using \<open>subgraph H G\<close> by (rule arcs_ends_mono)
  finally show "set (vwalk_arcs p) \<subseteq> arcs_ends G" .
qed

lemma vpathI_subgraph:
  assumes "vpath p G"
  assumes "subgraph G H"
  shows "vpath p H"
using assms by (auto intro: vwalkI_subgraph)

lemma (in loopfree_digraph) vpathI_arc:
  assumes "(a,b) \<in> arcs_ends G"
  shows "vpath [a,b] G"
using assms
by (intro vpathI vwalkI) (auto intro: adj_in_verts adj_not_same)

end
