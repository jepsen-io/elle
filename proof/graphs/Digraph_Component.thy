(* Title:  Digraph_Component.thy
   Author: Lars Noschinski, TU München
*)

theory Digraph_Component
imports
  Digraph
  Arc_Walk
  Pair_Digraph
begin

section \<open>Components of (Symmetric) Digraphs\<close>

definition compatible :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "compatible G H \<equiv> tail G = tail H \<and> head G = head H"

(* Require @{term "wf_digraph G"}? *)
definition subgraph :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "subgraph H G \<equiv> verts H \<subseteq> verts G \<and> arcs H \<subseteq> arcs G \<and> wf_digraph G \<and> wf_digraph H \<and> compatible G H"

definition induced_subgraph :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "induced_subgraph H G \<equiv> subgraph H G \<and> arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}"

definition spanning :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "spanning H G \<equiv> subgraph H G \<and> verts G = verts H"

definition strongly_connected :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "strongly_connected G \<equiv> verts G \<noteq> {} \<and> (\<forall>u \<in> verts G. \<forall>v \<in> verts G. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"


text \<open>
  The following function computes underlying symmetric graph of a digraph
  and removes parallel arcs.
\<close>

definition mk_symmetric :: "('a,'b) pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "mk_symmetric G \<equiv> \<lparr> pverts = verts G, parcs = \<Union>e\<in>arcs G. {(tail G e, head G e), (head G e, tail G e)}\<rparr>"

definition connected :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "connected G \<equiv> strongly_connected (mk_symmetric G)"

definition forest :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "forest G \<equiv> \<not>(\<exists>p. pre_digraph.cycle G p)"

definition tree :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "tree G \<equiv> connected G \<and> forest G"

definition spanning_tree :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "spanning_tree H G \<equiv> tree H \<and> spanning H G"

definition (in pre_digraph)
  max_subgraph :: "(('a,'b) pre_digraph \<Rightarrow> bool) \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow>  bool"
where
  "max_subgraph P H \<equiv> subgraph H G \<and> P H \<and> (\<forall>H'. H' \<noteq> H \<and> subgraph H H' \<longrightarrow> \<not>(subgraph H' G \<and> P H'))"

definition (in pre_digraph) sccs :: "('a,'b) pre_digraph set" where
  "sccs \<equiv> {H. induced_subgraph H G \<and> strongly_connected H \<and> \<not>(\<exists>H'. induced_subgraph H' G
      \<and> strongly_connected H' \<and> verts H \<subset> verts H')}"

definition (in pre_digraph) sccs_verts :: "'a set set" where
  "sccs_verts = {S. S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)}"
(*XXX:  "sccs_verts = verts ` sccs" *)

definition (in pre_digraph) scc_of :: "'a \<Rightarrow> 'a set" where
  "scc_of u \<equiv> {v. u \<rightarrow>\<^sup>* v \<and> v \<rightarrow>\<^sup>* u}"

definition union :: "('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> ('a,'b) pre_digraph" where
  "union G H \<equiv> \<lparr> verts = verts G \<union> verts H, arcs = arcs G \<union> arcs H, tail = tail G, head = head G\<rparr>"

definition (in pre_digraph) Union :: "('a,'b) pre_digraph set \<Rightarrow> ('a,'b) pre_digraph" where
  "Union gs = \<lparr> verts = (\<Union>G \<in> gs. verts G), arcs = (\<Union>G \<in> gs. arcs G),
    tail = tail G , head = head G  \<rparr>"



subsection \<open>Compatible Graphs\<close>

lemma compatible_tail:
  assumes "compatible G H" shows "tail G = tail H"
  using assms by (simp add: fun_eq_iff compatible_def)

lemma compatible_head:
  assumes "compatible G H" shows "head G = head H"
  using assms by (simp add: fun_eq_iff compatible_def)

lemma compatible_cas:
  assumes "compatible G H" shows "pre_digraph.cas G = pre_digraph.cas H"
proof (unfold fun_eq_iff, intro allI)
  fix u es v show "pre_digraph.cas G u es v = pre_digraph.cas H u es v"
    using assms
    by (induct es arbitrary: u)
       (simp_all add: pre_digraph.cas.simps compatible_head compatible_tail)
qed

lemma compatible_awalk_verts:
  assumes "compatible G H" shows "pre_digraph.awalk_verts G = pre_digraph.awalk_verts H"
proof (unfold fun_eq_iff, intro allI)
  fix u es show "pre_digraph.awalk_verts G u es = pre_digraph.awalk_verts H u es"
    using assms
    by (induct es arbitrary: u)
       (simp_all add: pre_digraph.awalk_verts.simps compatible_head compatible_tail)
qed

lemma compatibleI_with_proj[intro]:
  shows "compatible (with_proj G) (with_proj H)"
  by (auto simp: compatible_def)



subsection \<open>Basic lemmas\<close>

lemma (in sym_digraph) graph_symmetric:
  shows "(u,v) \<in> arcs_ends G \<Longrightarrow> (v,u) \<in> arcs_ends G"
  using sym_arcs by (auto simp add: symmetric_def sym_def)

lemma strongly_connectedI[intro]:
  assumes "verts G \<noteq> {}" "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "strongly_connected G"
using assms by (simp add: strongly_connected_def)

lemma strongly_connectedE[elim]:
  assumes "strongly_connected G"
  assumes "(\<And>u v. u \<in> verts G \<and> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: strongly_connected_def)

lemma subgraph_imp_subverts:
  assumes "subgraph H G"
  shows "verts H \<subseteq> verts G"
using assms by (simp add: subgraph_def)

lemma induced_imp_subgraph:
  assumes "induced_subgraph H G"
  shows "subgraph H G"
using assms by (simp add: induced_subgraph_def)

lemma (in pre_digraph) in_sccs_imp_induced:
  assumes "c \<in> sccs"
  shows "induced_subgraph c G"
using assms by (auto simp: sccs_def)

lemma spanning_tree_imp_tree[dest]:
  assumes "spanning_tree H G"
  shows "tree H"
using assms by (simp add: spanning_tree_def)

lemma tree_imp_connected[dest]:
  assumes "tree G"
  shows "connected G"
using assms by (simp add: tree_def)

lemma spanning_treeI[intro]:
  assumes "spanning H G"
  assumes "tree H"
  shows "spanning_tree H G"
using assms by (simp add: spanning_tree_def)

lemma spanning_treeE[elim]:
  assumes "spanning_tree H G"
  assumes "tree H \<and> spanning H G \<Longrightarrow> P"
  shows "P"
using assms by (simp add: spanning_tree_def)

lemma spanningE[elim]:
  assumes "spanning H G"
  assumes "subgraph H G \<and> verts G = verts H \<Longrightarrow> P"
  shows "P"
using assms by (simp add: spanning_def)

lemma (in pre_digraph) in_sccsI[intro]:
  assumes "induced_subgraph c G"
  assumes "strongly_connected c"
  assumes "\<not>(\<exists>c'. induced_subgraph c' G \<and> strongly_connected c' \<and>
    verts c \<subset> verts c')"
  shows "c \<in> sccs"
using assms by (auto simp add: sccs_def)

lemma (in pre_digraph) in_sccsE[elim]:
  assumes "c \<in> sccs"
  assumes "induced_subgraph c G \<Longrightarrow> strongly_connected c \<Longrightarrow> \<not> (\<exists>d.
    induced_subgraph d G \<and> strongly_connected d \<and> verts c \<subset> verts d) \<Longrightarrow> P"
  shows "P"
using assms by (simp add: sccs_def)

lemma subgraphI:
  assumes "verts H \<subseteq> verts G"
  assumes "arcs H \<subseteq> arcs G"
  assumes "compatible G H"
  assumes "wf_digraph H"
  assumes "wf_digraph G"
  shows "subgraph H G"
using assms by (auto simp add: subgraph_def)

lemma subgraphE[elim]:
  assumes "subgraph H G"
  obtains "verts H \<subseteq> verts G" "arcs H \<subseteq> arcs G" "compatible G H" "wf_digraph H" "wf_digraph G"
using assms by (simp add: subgraph_def)

lemma induced_subgraphI[intro]:
  assumes "subgraph H G"
  assumes "arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}"
  shows "induced_subgraph H G"
using assms unfolding induced_subgraph_def by safe

lemma induced_subgraphE[elim]:
  assumes "induced_subgraph H G"
  assumes "\<lbrakk>subgraph H G; arcs H = {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: induced_subgraph_def)

lemma pverts_mk_symmetric[simp]: "pverts (mk_symmetric G) = verts G"
  and parcs_mk_symmetric:
    "parcs (mk_symmetric G) = (\<Union>e\<in>arcs G. {(tail G e, head G e), (head G e, tail G e)})"
  by (auto simp: mk_symmetric_def arcs_ends_conv image_UN)

lemma arcs_ends_mono:
  assumes "subgraph H G"
  shows "arcs_ends H \<subseteq> arcs_ends G"
  using assms by (auto simp add: subgraph_def arcs_ends_conv compatible_tail compatible_head)

lemma (in wf_digraph) subgraph_refl: "subgraph G G"
  by (auto simp: subgraph_def compatible_def) unfold_locales

lemma (in wf_digraph) induced_subgraph_refl: "induced_subgraph G G"
  by (rule induced_subgraphI) (auto simp: subgraph_refl)




subsection \<open>The underlying symmetric graph of a digraph\<close>

lemma (in wf_digraph) wellformed_mk_symmetric[intro]: "pair_wf_digraph (mk_symmetric G)"
  by unfold_locales (auto simp: parcs_mk_symmetric)

lemma (in fin_digraph) pair_fin_digraph_mk_symmetric[intro]: "pair_fin_digraph (mk_symmetric G)"
proof -
  have "finite ((\<lambda>(a,b). (b,a)) ` arcs_ends G)" (is "finite ?X") by (auto simp: arcs_ends_conv)
  also have "?X = {(a, b). (b, a) \<in> arcs_ends G}" by auto
  finally have X: "finite ..." .
  then show ?thesis
    by unfold_locales (auto simp: mk_symmetric_def arcs_ends_conv)
qed

lemma (in digraph) digraph_mk_symmetric[intro]: "pair_digraph (mk_symmetric G)"
proof -
  have "finite ((\<lambda>(a,b). (b,a)) ` arcs_ends G)" (is "finite ?X") by (auto simp: arcs_ends_conv)
  also have "?X = {(a, b). (b, a) \<in> arcs_ends G}" by auto
  finally have "finite ..." .
  then show ?thesis
    by unfold_locales (auto simp: mk_symmetric_def arc_to_ends_def dest: no_loops)
qed

lemma (in wf_digraph) reachable_mk_symmetricI:
  assumes "u \<rightarrow>\<^sup>* v" shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
proof -
  have "arcs_ends G \<subseteq> parcs (mk_symmetric G)"
       "(u, v) \<in> rtrancl_on (pverts (mk_symmetric G)) (arcs_ends G)"
    using assms unfolding reachable_def by (auto simp: parcs_mk_symmetric)
  then show ?thesis unfolding reachable_def by (auto intro: rtrancl_on_mono)
qed

lemma (in wf_digraph) adj_mk_symmetric_eq:
  "symmetric G \<Longrightarrow> parcs (mk_symmetric G) = arcs_ends G"
  by (auto simp: parcs_mk_symmetric in_arcs_imp_in_arcs_ends arcs_ends_symmetric)

lemma (in wf_digraph) reachable_mk_symmetric_eq:
  assumes "symmetric G" shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>* v" (is "?L \<longleftrightarrow> ?R")
  using adj_mk_symmetric_eq[OF assms] unfolding reachable_def by auto

lemma (in wf_digraph) mk_symmetric_awalk_imp_awalk:
  assumes sym: "symmetric G"
  assumes walk: "pre_digraph.awalk (mk_symmetric G) u p v"
  obtains q where "awalk u q v"
proof -
  interpret S: pair_wf_digraph "mk_symmetric G" ..
  from walk have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
    by (simp only: S.reachable_awalk) rule
  then have "u \<rightarrow>\<^sup>* v" by (simp only: reachable_mk_symmetric_eq[OF sym])
  then show ?thesis by (auto simp: reachable_awalk intro: that)
qed

lemma symmetric_mk_symmetric:
  "symmetric (mk_symmetric G)"
  by (auto simp: symmetric_def parcs_mk_symmetric intro: symI)



subsection \<open>Subgraphs and Induced Subgraphs\<close>

lemma subgraph_trans:
  assumes "subgraph G H" "subgraph H I" shows "subgraph G I"
  using assms by (auto simp: subgraph_def compatible_def)

text \<open>
  The @{term digraph} and @{term fin_digraph} properties are preserved under
  the (inverse) subgraph relation
\<close>
lemma (in fin_digraph) fin_digraph_subgraph:
  assumes "subgraph H G" shows "fin_digraph H"
proof (intro_locales)
  from assms show "wf_digraph H" by auto

  have HG: "arcs H \<subseteq> arcs G" "verts H \<subseteq> verts G"
    using assms by auto
  then have "finite (verts H)" "finite (arcs H)"
    using finite_verts finite_arcs by (blast intro: finite_subset)+
  then show "fin_digraph_axioms H"
    by unfold_locales
qed

lemma (in digraph) digraph_subgraph:
  assumes "subgraph H G" shows "digraph H"
proof
  fix e assume e: "e \<in> arcs H"
  with assms show "tail H e \<in> verts H" "head H e \<in> verts H"
    by (auto simp: subgraph_def intro: wf_digraph.wellformed)
  from e and assms have "e \<in> arcs H \<inter> arcs G" by auto
  with assms show "tail H e \<noteq> head H e"
    using no_loops by (auto simp: subgraph_def compatible_def arc_to_ends_def)
next
  have "arcs H \<subseteq> arcs G" "verts H \<subseteq> verts G" using assms by auto
  then show "finite (arcs H)" "finite (verts H)"
    using finite_verts finite_arcs by (blast intro: finite_subset)+
next
  fix e1 e2 assume "e1 \<in> arcs H" "e2 \<in> arcs H"
    and eq: "arc_to_ends H e1 = arc_to_ends H e2"
  with assms have "e1 \<in> arcs H \<inter> arcs G" "e2 \<in> arcs H \<inter> arcs G"
    by auto
  with eq show "e1 = e2"
    using no_multi_arcs assms
    by (auto simp: subgraph_def compatible_def arc_to_ends_def)
qed

lemma (in pre_digraph) adj_mono:
  assumes "u \<rightarrow>\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow> v"
  using assms by (blast dest: arcs_ends_mono)

lemma (in pre_digraph) reachable_mono:
  assumes walk: "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" and sub: "subgraph H G"
  shows "u \<rightarrow>\<^sup>* v"
proof -
  have "verts H \<subseteq> verts G" using sub by auto
  with assms show ?thesis
    unfolding reachable_def by (metis arcs_ends_mono rtrancl_on_mono)
qed


text \<open>
  Arc walks and paths are preserved under the subgraph relation.
\<close>
lemma (in wf_digraph) subgraph_awalk_imp_awalk:
  assumes walk: "pre_digraph.awalk H u p v"
  assumes sub: "subgraph H G"
  shows "awalk u p v"
  using assms by (auto simp: pre_digraph.awalk_def compatible_cas)

lemma (in wf_digraph) subgraph_apath_imp_apath:
  assumes path: "pre_digraph.apath H u p v"
  assumes sub: "subgraph H G"
  shows "apath u p v"
  using assms unfolding pre_digraph.apath_def
  by (auto intro: subgraph_awalk_imp_awalk simp: compatible_awalk_verts)

lemma subgraph_mk_symmetric:
  assumes "subgraph H G"
  shows "subgraph (mk_symmetric H) (mk_symmetric G)"
proof (rule subgraphI)
  let ?wpms = "\<lambda>G. mk_symmetric G"
  from assms have "compatible G H" by auto
  with assms
  show "verts (?wpms H)  \<subseteq> verts (?wpms G)"
    and "arcs (?wpms H) \<subseteq> arcs (?wpms G)"
    by (auto simp: parcs_mk_symmetric compatible_head compatible_tail)
  show "compatible (?wpms G) (?wpms H)" by rule
  interpret H: pair_wf_digraph "mk_symmetric H"
    using assms by (auto intro: wf_digraph.wellformed_mk_symmetric)
  interpret G: pair_wf_digraph "mk_symmetric G"
    using assms by (auto intro: wf_digraph.wellformed_mk_symmetric)
  show "wf_digraph (?wpms H)"
    by unfold_locales
  show "wf_digraph (?wpms G)" by unfold_locales
qed

lemma (in fin_digraph) subgraph_in_degree:
  assumes "subgraph H G"
  shows "in_degree H v \<le> in_degree G v"
proof -
  have "finite (in_arcs G v)" by auto
  moreover
  have "in_arcs H v \<subseteq> in_arcs G v"
    using assms by (auto simp: subgraph_def in_arcs_def compatible_head compatible_tail)
  ultimately
  show ?thesis unfolding in_degree_def by (rule card_mono)
qed

lemma (in wf_digraph) subgraph_cycle:
  assumes "subgraph H G" "pre_digraph.cycle H p " shows "cycle p"
proof -
  from assms have "compatible G H" by auto
  with assms show ?thesis
    by (auto simp: pre_digraph.cycle_def compatible_awalk_verts intro: subgraph_awalk_imp_awalk)
qed

lemma (in wf_digraph) subgraph_del_vert: "subgraph (del_vert u) G"
  by (auto simp: subgraph_def compatible_def del_vert_simps wf_digraph_del_vert) intro_locales

lemma (in wf_digraph) subgraph_del_arc: "subgraph (del_arc a) G"
  by (auto simp: subgraph_def compatible_def del_vert_simps wf_digraph_del_vert) intro_locales



subsection \<open>Induced subgraphs\<close>

lemma wf_digraphI_induced:
  assumes "induced_subgraph H G"
  shows "wf_digraph H"
proof -
  from assms have "compatible G H" by auto
  with assms show ?thesis by unfold_locales (auto simp: compatible_tail compatible_head)
qed

lemma (in digraph) digraphI_induced:
  assumes "induced_subgraph H G"
  shows "digraph H"
proof -
  interpret W: wf_digraph H using assms by (rule wf_digraphI_induced)
  from assms have "compatible G H" by auto
  from assms have arcs: "arcs H \<subseteq> arcs G" by blast
  show ?thesis
  proof
    from assms have "verts H \<subseteq> verts G" by blast
    then show "finite (verts H)" using finite_verts by (rule finite_subset)
  next
    from arcs show "finite (arcs H)" using finite_arcs by (rule finite_subset)
  next
    fix e assume "e \<in> arcs H"
    with arcs \<open>compatible G H\<close> show "tail H e \<noteq> head H e"
      by (auto dest: no_loops simp: compatible_tail[symmetric] compatible_head[symmetric])
  next
    fix e1 e2 assume "e1 \<in> arcs H" "e2 \<in> arcs H" and ate: "arc_to_ends H e1 = arc_to_ends H e2"
    with arcs \<open>compatible G H\<close> show "e1 = e2" using ate
      by (auto intro: no_multi_arcs simp: compatible_tail[symmetric] compatible_head[symmetric] arc_to_ends_def)
  qed
qed

text \<open>Computes the subgraph of @{term G} induced by @{term vs}\<close>
definition induce_subgraph :: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pre_digraph" (infix "\<restriction>" 67) where
  "G \<restriction> vs = \<lparr> verts = vs, arcs = {e \<in> arcs G. tail G e \<in> vs \<and> head G e \<in> vs},
    tail = tail G, head = head G \<rparr>"

lemma induce_subgraph_verts[simp]:
 "verts (G \<restriction> vs) = vs"
by (auto simp add: induce_subgraph_def)

lemma induce_subgraph_arcs[simp]:
 "arcs (G \<restriction> vs) = {e \<in> arcs G. tail G e \<in> vs \<and> head G e \<in> vs}"
by (auto simp add: induce_subgraph_def)

lemma induce_subgraph_tail[simp]:
  "tail (G \<restriction> vs) = tail G"
by (auto simp: induce_subgraph_def)

lemma induce_subgraph_head[simp]:
  "head (G \<restriction> vs) = head G"
by (auto simp: induce_subgraph_def)

lemma compatible_induce_subgraph: "compatible (G \<restriction> S) G"
  by (auto simp: compatible_def)

lemma (in wf_digraph) induced_induce[intro]:
  assumes "vs \<subseteq> verts G"
  shows "induced_subgraph (G \<restriction> vs) G"
using assms
by (intro subgraphI induced_subgraphI)
   (auto simp: arc_to_ends_def induce_subgraph_def wf_digraph_def compatible_def)

lemma (in wf_digraph) wellformed_induce_subgraph[intro]:
  "wf_digraph (G \<restriction> vs)"
  by unfold_locales auto

lemma induced_graph_imp_symmetric:
  assumes "symmetric G"
  assumes "induced_subgraph H G"
  shows "symmetric H"
proof (unfold symmetric_conv, safe)
  from assms have "compatible G H" by auto

  fix e1 assume "e1 \<in> arcs H"
  then obtain e2 where "tail G e1 = head G e2"  "head G e1 = tail G e2" "e2 \<in> arcs G"
    using assms by (auto simp add: symmetric_conv)
  moreover
  then have "e2 \<in> arcs H"
    using assms and \<open>e1 \<in> arcs H\<close> by auto
  ultimately
  show "\<exists>e2\<in>arcs H. tail H e1 = head H e2 \<and> head H e1 = tail H e2"
    using assms \<open>e1 \<in> arcs H\<close> \<open>compatible G H\<close>
    by (auto simp: compatible_head compatible_tail)
qed

lemma (in sym_digraph) induced_graph_imp_graph:
  assumes "induced_subgraph H G"
  shows "sym_digraph H"
proof (rule wf_digraph.sym_digraphI)
  from assms show "wf_digraph H" by (rule wf_digraphI_induced)
next
  show "symmetric H"
    using assms sym_arcs by (auto intro: induced_graph_imp_symmetric)
qed

lemma (in wf_digraph) induce_reachable_preserves_paths:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {w. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w}\<^esub> v"
  using assms
proof induct
  case base then show ?case by (auto simp: reachable_def)
next
  case (step u w)
  interpret iG: wf_digraph "G \<restriction> {w. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w}"
    by (rule wellformed_induce_subgraph)
  from \<open>u \<rightarrow> w\<close> have "u \<rightarrow>\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> wa}\<^esub> w"
    by (auto simp: arcs_ends_conv reachable_def intro: wellformed rtrancl_on_into_rtrancl_on)
  then have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> wa}\<^esub> w"
    by (rule iG.reachable_adjI)
  moreover
  from step have "{x. w \<rightarrow>\<^sup>* x} \<subseteq> {x. u \<rightarrow>\<^sup>* x}"
    by (auto intro: adj_reachable_trans)
  then have "subgraph (G \<restriction> {wa. w \<rightarrow>\<^sup>* wa}) (G \<restriction> {wa. u \<rightarrow>\<^sup>* wa})"
    by (intro subgraphI) (auto simp: arcs_ends_conv compatible_def)
  then have "w \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {wa. u \<rightarrow>\<^sup>* wa}\<^esub> v"
    by (rule iG.reachable_mono[rotated]) fact
  ultimately show ?case by (rule iG.reachable_trans)
qed

lemma induce_subgraph_ends[simp]:
  "arc_to_ends (G \<restriction> S) = arc_to_ends G"
  by (auto simp: arc_to_ends_def)

lemma dominates_induce_subgraphD:
  assumes "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v" shows "u \<rightarrow>\<^bsub>G\<^esub> v"
  using assms by (auto simp: arcs_ends_def intro: rev_image_eqI)

context wf_digraph begin

  lemma reachable_induce_subgraphD:
    assumes "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> verts G" shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  proof -
    interpret GS: wf_digraph "G \<restriction> S" by auto
    show ?thesis
      using assms by induct (auto dest: dominates_induce_subgraphD intro: adj_reachable_trans)
  qed

  lemma dominates_induce_ss:
    assumes "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> T" shows "u \<rightarrow>\<^bsub>G \<restriction> T\<^esub> v"
    using assms by (auto simp: arcs_ends_def)

  lemma reachable_induce_ss:
    assumes "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> T" shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
    using assms unfolding reachable_def
    by induct (auto intro: dominates_induce_ss converse_rtrancl_on_into_rtrancl_on)

  lemma awalk_verts_induce:
    "pre_digraph.awalk_verts (G \<restriction> S) = awalk_verts"
  proof (intro ext)
    fix u p show "pre_digraph.awalk_verts (G \<restriction> S) u p = awalk_verts u p"
      by (induct p arbitrary: u) (auto simp: pre_digraph.awalk_verts.simps)
  qed

  lemma (in -) cas_subset:
    assumes "pre_digraph.cas G u p v" "subgraph G H"
    shows "pre_digraph.cas H u p v"
    using assms
    by (induct p arbitrary: u) (auto simp: pre_digraph.cas.simps subgraph_def compatible_def)

  lemma cas_induce:
    assumes "cas u p v" "set (awalk_verts u p) \<subseteq> S"
    shows "pre_digraph.cas (G \<restriction> S) u p v"
    using assms
  proof (induct p arbitrary: u S)
    case Nil then show ?case by (auto simp: pre_digraph.cas.simps)
  next
    case (Cons a as)
    have "pre_digraph.cas (G \<restriction> set (awalk_verts (head G a) as)) (head G a) as v"
      using Cons by auto
    then have "pre_digraph.cas (G \<restriction> S) (head G a) as v"
      using \<open>_ \<subseteq> S\<close> by (rule_tac cas_subset) (auto simp: subgraph_def compatible_def)
    then show ?case using Cons by (auto simp: pre_digraph.cas.simps)
  qed

  lemma awalk_induce:
    assumes "awalk u p v" "set (awalk_verts u p) \<subseteq> S"
    shows "pre_digraph.awalk (G \<restriction> S) u p v"
  proof -
    interpret GS: wf_digraph "G \<restriction> S" by auto
    show ?thesis
      using assms by (auto simp: pre_digraph.awalk_def cas_induce GS.cas_induce set_awalk_verts)
  qed

  lemma subgraph_induce_subgraphI:
    assumes "V \<subseteq> verts G" shows "subgraph (G \<restriction> V) G"
    by (metis assms induced_imp_subgraph induced_induce)

end

lemma induced_subgraphI':
  assumes subg:"subgraph H G"
  assumes max: "\<And>H'. subgraph H' G \<Longrightarrow> (verts H' \<noteq> verts H \<or> arcs H' \<subseteq> arcs H)"
  shows "induced_subgraph H G"
proof -
  interpret H: wf_digraph H using \<open>subgraph H G\<close> ..
  define H' where "H' = G \<restriction> verts H"
  then have H'_props: "subgraph H' G" "verts H' = verts H"
    using subg by (auto intro: wf_digraph.subgraph_induce_subgraphI)
  moreover
  have "arcs H' = arcs H"
  proof
    show "arcs H' \<subseteq> arcs H" using max H'_props by auto
    show "arcs H \<subseteq> arcs H'" using subg by (auto simp: H'_def compatible_def)
  qed
  then show "induced_subgraph H G" by (auto simp: induced_subgraph_def H'_def subg) 
qed

lemma (in pre_digraph) induced_subgraph_altdef:
  "induced_subgraph H G \<longleftrightarrow> subgraph H G \<and> (\<forall>H'. subgraph H' G \<longrightarrow> (verts H' \<noteq> verts H \<or> arcs H' \<subseteq> arcs H))" (is "?L \<longleftrightarrow> ?R")
proof -
  { fix H' :: "('a,'b) pre_digraph"
    assume A: "verts H' = verts H" "subgraph H' G"
    interpret H': wf_digraph H' using \<open>subgraph H' G\<close> ..
    from \<open>subgraph H' G\<close>
    have comp: "tail G = tail H'" "head G = head H'" by (auto simp: compatible_def)
    then have "\<And>a. a \<in> arcs H' \<Longrightarrow> tail G a \<in> verts H" "\<And>a. a \<in> arcs H' \<Longrightarrow> tail G a \<in> verts H"
      by (auto dest: H'.wellformed simp: A)
    then have "arcs H' \<subseteq> {e \<in> arcs G. tail G e \<in> verts H \<and> head G e \<in> verts H}"
      using \<open>subgraph H' G\<close> by (auto simp: subgraph_def comp A(1)[symmetric])
  }
  then show ?thesis using induced_subgraphI'[of H G] by (auto simp: induced_subgraph_def)
qed



subsection \<open>Unions of Graphs\<close>

lemma
  verts_union[simp]: "verts (union G H) = verts G \<union> verts H" and
  arcs_union[simp]: "arcs (union G H) = arcs G \<union> arcs H" and
  tail_union[simp]: "tail (union G H) = tail G" and
  head_union[simp]: "head (union G H) = head G"
  by (auto simp: union_def)

lemma wellformed_union:
  assumes "wf_digraph G" "wf_digraph H" "compatible G H"
  shows "wf_digraph (union G H)"
  using assms
  by unfold_locales
     (auto simp: union_def compatible_tail compatible_head dest: wf_digraph.wellformed)

lemma subgraph_union_iff:
  assumes "wf_digraph H1" "wf_digraph H2" "compatible H1 H2"
  shows "subgraph (union H1 H2) G \<longleftrightarrow> subgraph H1 G \<and> subgraph H2 G"
  using assms by (fastforce simp: compatible_def intro!: subgraphI wellformed_union)

lemma subgraph_union[intro]:
  assumes "subgraph H1 G" "compatible H1 G"
  assumes "subgraph H2 G" "compatible H2 G"
  shows "subgraph (union H1 H2) G"
proof -
  from assms have "wf_digraph (union H1 H2)"
    by (auto intro: wellformed_union simp: compatible_def)
  with assms show ?thesis
    by (auto simp add: subgraph_def union_def arc_to_ends_def compatible_def)
qed

lemma union_fin_digraph:
  assumes "fin_digraph G" "fin_digraph H" "compatible G H"
  shows "fin_digraph (union G H)"
proof intro_locales
  interpret G: fin_digraph G by (rule assms)
  interpret H: fin_digraph H by (rule assms)
  show "wf_digraph (union G H)" using assms
    by (intro wellformed_union) intro_locales
  show "fin_digraph_axioms (union G H)"
    using assms by unfold_locales (auto simp: union_def)
qed

lemma subgraphs_of_union:
  assumes "wf_digraph G" "wf_digraph G'" "compatible G G'"
  shows "subgraph G (union G G')"
    and "subgraph G' (union G G')"
  using assms by (auto intro!: subgraphI wellformed_union simp: compatible_def)


subsection \<open>Maximal Subgraphs\<close>

lemma (in pre_digraph) max_subgraph_mp:
  assumes "max_subgraph Q x" "\<And>x. P x \<Longrightarrow> Q x" "P x" shows "max_subgraph P x"
  using assms by (auto simp: max_subgraph_def)

lemma (in pre_digraph) max_subgraph_prop: "max_subgraph P x \<Longrightarrow> P x"
  by (simp add: max_subgraph_def)

lemma (in pre_digraph) max_subgraph_subg_eq:
  assumes "max_subgraph P H1" "max_subgraph P H2" "subgraph H1 H2"
  shows "H1 = H2"
  using assms by (auto simp: max_subgraph_def)

lemma subgraph_induce_subgraphI2:
  assumes "subgraph H G" shows "subgraph H (G \<restriction> verts H)"
  using assms by (auto simp: subgraph_def compatible_def wf_digraph.wellformed wf_digraph.wellformed_induce_subgraph)

definition arc_mono :: "(('a,'b) pre_digraph \<Rightarrow> bool) \<Rightarrow> bool" where
  "arc_mono P \<equiv> (\<forall>H1 H2. P H1 \<and> subgraph H1 H2 \<and> verts H1 = verts H2 \<longrightarrow> P H2)"

lemma (in pre_digraph) induced_subgraphI_arc_mono:
  assumes "max_subgraph P H"
  assumes "arc_mono P"
  shows "induced_subgraph H G"
proof -
  interpret wf_digraph G using assms by (auto simp: max_subgraph_def)
  have "subgraph H (G \<restriction> verts H)" "subgraph (G \<restriction> verts H) G" "verts H = verts (G \<restriction> verts H)" "P H"
    using assms by (auto simp: max_subgraph_def subgraph_induce_subgraphI2 subgraph_induce_subgraphI)
  moreover
  then have "P (G \<restriction> verts  H)"
    using assms by (auto simp: arc_mono_def)
  ultimately
  have "max_subgraph P (G \<restriction> verts H)"
    using assms by (auto simp: max_subgraph_def) metis
  then have "H = G \<restriction> verts H"
    using \<open>max_subgraph P H\<close> \<open>subgraph H _\<close>
    by (intro max_subgraph_subg_eq)
  show ?thesis using assms by (subst \<open>H = _\<close>) (auto simp: max_subgraph_def)
qed

lemma (in pre_digraph) induced_subgraph_altdef2:
  "induced_subgraph H G \<longleftrightarrow> max_subgraph (\<lambda>H'. verts H' = verts H) H" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  moreover
  { fix H' assume "induced_subgraph H G" "subgraph H H'" "H \<noteq> H'"
    then have "\<not>(subgraph H' G \<and> verts H' = verts H)"
      by (auto simp: induced_subgraph_altdef compatible_def elim!: allE[where x=H'])
  }
  ultimately show "max_subgraph (\<lambda>H'. verts H' = verts H) H" by (auto simp: max_subgraph_def)
next
  assume ?R
  moreover have "arc_mono (\<lambda>H'. verts H' = verts H)" by (auto simp: arc_mono_def)
  ultimately show ?L by (rule induced_subgraphI_arc_mono)
qed

(*XXX*)
lemma (in pre_digraph) max_subgraphI:
  assumes "P x" "subgraph x G" "\<And>y. \<lbrakk>x \<noteq> y; subgraph x y; subgraph y G\<rbrakk> \<Longrightarrow> \<not>P y"
  shows "max_subgraph P x"
  using assms by (auto simp: max_subgraph_def)

lemma (in pre_digraph) subgraphI_max_subgraph: "max_subgraph P x \<Longrightarrow> subgraph x G"
  by (simp add: max_subgraph_def)


subsection \<open>Connected and Strongly Connected Graphs\<close>

context wf_digraph begin

  lemma in_sccs_verts_conv_reachable:
    "S \<in> sccs_verts \<longleftrightarrow> S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
    by (simp add: sccs_verts_def)

  lemma sccs_verts_disjoint:
    assumes "S \<in> sccs_verts" "T \<in> sccs_verts" "S \<noteq> T" shows "S \<inter> T = {}"
    using assms unfolding in_sccs_verts_conv_reachable by safe meson+

  lemma strongly_connected_spanning_imp_strongly_connected:
    assumes "spanning H G"
    assumes "strongly_connected H"
    shows "strongly_connected G"
  proof (unfold strongly_connected_def, intro ballI conjI)
    from assms show "verts G \<noteq> {}" unfolding strongly_connected_def spanning_def by auto
  next
    fix u v assume "u \<in> verts G" and "v \<in> verts G"
    then have "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" "subgraph H G"
      using assms by (auto simp add: strongly_connected_def)
    then show "u \<rightarrow>\<^sup>* v" by (rule reachable_mono)
  qed

  lemma strongly_connected_imp_induce_subgraph_strongly_connected:
    assumes subg: "subgraph H G"
    assumes sc: "strongly_connected H"
    shows "strongly_connected (G \<restriction> (verts H))"
  proof -
    let ?is_H = "G \<restriction> (verts H)"

    interpret H: wf_digraph H
      using subg by (rule subgraphE)
    interpret GrH: wf_digraph "?is_H"
      by (rule wellformed_induce_subgraph)

    have "verts H \<subseteq> verts G" using assms by auto

    have "subgraph H (G \<restriction> verts H)"
      using subg by (intro subgraphI) (auto simp: compatible_def)
    then show ?thesis
      using induced_induce[OF \<open>verts H \<subseteq> verts G\<close>]
        and sc GrH.strongly_connected_spanning_imp_strongly_connected
      unfolding spanning_def by auto
  qed

  lemma in_sccs_vertsI_sccs:
    assumes "S \<in> verts ` sccs" shows "S \<in> sccs_verts"
    unfolding sccs_verts_def
  proof (intro CollectI conjI allI ballI impI)
    show "S \<noteq> {}" using assms by (auto simp: sccs_verts_def sccs_def strongly_connected_def)

    from assms have sc: "strongly_connected (G \<restriction> S)" "S \<subseteq> verts G"
      apply (auto simp: sccs_verts_def sccs_def)
      by (metis induced_imp_subgraph subgraphE wf_digraph.strongly_connected_imp_induce_subgraph_strongly_connected)

    {
      fix u v assume A: "u \<in> S" "v \<in> S"
      with sc have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v" by auto
      then show "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" using \<open>S \<subseteq> verts G\<close> by (rule reachable_induce_subgraphD)
    next
      fix u v assume A: "u \<in> S" "v \<notin> S"
      { assume B: "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
        from B obtain p_uv where p_uv: "awalk u p_uv v" by (metis reachable_awalk)
        from B obtain p_vu where p_vu: "awalk v p_vu u" by (metis reachable_awalk)
        define T where "T = S \<union> set (awalk_verts u p_uv) \<union> set (awalk_verts v p_vu)"
        have "S \<subseteq> T" by (auto simp: T_def)
        have "v \<in> T" using p_vu by (auto simp: T_def set_awalk_verts)
        then have "T \<noteq> S" using \<open>v \<notin> S\<close> by auto

        interpret T: wf_digraph "G \<restriction> T" by auto

        from p_uv have T_p_uv: "T.awalk u p_uv v"
          by (rule awalk_induce) (auto simp: T_def)
        from p_vu have T_p_vu: "T.awalk v p_vu u"
          by (rule awalk_induce) (auto simp: T_def)

        have uv_reach: "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> u"
          using T_p_uv T_p_vu A by (metis T.reachable_awalk)+

        { fix x y assume "x \<in> S" "y \<in> S"
          then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> y" "y \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> x"
            using sc by auto
          then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> y" "y \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
            using \<open>S \<subseteq> T\<close> by (auto intro: reachable_induce_ss)
        } note A1 = this

        { fix x assume "x \<in> T"
          moreover
          { assume "x \<in> S" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
              using uv_reach A1 A by (auto intro: T.reachable_trans[rotated])
          } moreover
          { assume "x \<in> set (awalk_verts u p_uv)" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
              using T_p_uv by (auto simp: awalk_verts_induce intro: T.awalk_verts_reachable_to)
          } moreover
          { assume "x \<in> set (awalk_verts v p_vu)" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
              using T_p_vu by (rule_tac T.reachable_trans)
                (auto simp: uv_reach awalk_verts_induce dest: T.awalk_verts_reachable_to)
          } ultimately
          have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" by (auto simp: T_def)
        } note xv_reach = this

        { fix x assume "x \<in> T"
          moreover
          { assume "x \<in> S" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
              using uv_reach A1 A by (auto intro: T.reachable_trans)
          } moreover
          { assume "x \<in> set (awalk_verts v p_vu)" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
              using T_p_vu by (auto simp: awalk_verts_induce intro: T.awalk_verts_reachable_from)
          } moreover
          { assume "x \<in> set (awalk_verts u p_uv)" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
              using T_p_uv by (rule_tac T.reachable_trans[rotated])
                (auto intro: T.awalk_verts_reachable_from uv_reach simp: awalk_verts_induce)
          } ultimately
          have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x" by (auto simp: T_def)
        } note vx_reach = this

        { fix x y assume "x \<in> T" "y \<in> T" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> y"
            using xv_reach vx_reach by (blast intro: T.reachable_trans)
        }
        then have "strongly_connected (G \<restriction> T)"
          using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> by auto
        moreover have "induced_subgraph (G \<restriction> T) G"
          using \<open>S \<subseteq> verts G\<close>
          by (auto simp: T_def intro: awalk_verts_reachable_from p_uv p_vu reachable_in_verts(2))
        ultimately
        have "\<exists>T. induced_subgraph (G \<restriction> T) G \<and> strongly_connected (G \<restriction> T) \<and> verts (G \<restriction> S) \<subset> verts (G \<restriction> T)"
          using \<open>S \<subseteq> T\<close> \<open>T \<noteq> S\<close> by auto
        then have "G \<restriction> S \<notin> sccs" unfolding sccs_def by blast
        then have "S \<notin> verts ` sccs"
          by (metis (erased, hide_lams) \<open>S \<subseteq> T\<close> \<open>T \<noteq> S\<close> \<open>induced_subgraph (G \<restriction> T) G\<close> \<open>strongly_connected (G \<restriction> T)\<close>
            dual_order.order_iff_strict image_iff in_sccsE induce_subgraph_verts)
        then have False using assms by metis
      }
      then show "\<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" by metis
    }
  qed

end

lemma arc_mono_strongly_connected[intro,simp]: "arc_mono strongly_connected"
  by (auto simp: arc_mono_def) (metis spanning_def subgraphE wf_digraph.strongly_connected_spanning_imp_strongly_connected)

lemma (in pre_digraph) sccs_altdef2:
  "sccs = {H. max_subgraph strongly_connected H}" (is "?L = ?R")
proof -
  { fix H H' :: "('a, 'b) pre_digraph" 
    assume a1: "strongly_connected H'"
    assume a2: "induced_subgraph H' G"
    assume a3: "max_subgraph strongly_connected H"
    assume a4: "verts H \<subseteq> verts H'"
    have sg: "subgraph H G" and ends_G: "tail G = tail H " "head G = head H"
      using a3 by (auto simp: max_subgraph_def compatible_def)
    then interpret H: wf_digraph H by blast
    have "arcs H \<subseteq> arcs H'" using a2 a4 sg by (fastforce simp: ends_G)
    then have "H = H'"
      using a1 a2 a3 a4
      by (metis (no_types) compatible_def induced_imp_subgraph max_subgraph_def subgraph_def)
  } note X = this

  { fix H
    assume a1: "induced_subgraph H G"
    assume a2: "strongly_connected H"
    assume a3: "\<forall>H'. strongly_connected H' \<longrightarrow> induced_subgraph H' G \<longrightarrow> \<not> verts H \<subset> verts H'"
    interpret G: wf_digraph G using a1 by auto
    { fix y assume "H \<noteq> y" and subg: "subgraph H y" "subgraph y G"
      then have "verts H \<subset> verts y"
        using a1 by (auto simp: induced_subgraph_altdef2 max_subgraph_def)
      then have "\<not>strongly_connected y"
        using subg a1 a2 a3[THEN spec, of "G \<restriction> verts y"]
        by (auto simp: G.induced_induce G.strongly_connected_imp_induce_subgraph_strongly_connected)
    }
    then have "max_subgraph strongly_connected H"
      using a1 a2 by (auto intro: max_subgraphI)
  } note Y = this

  show ?thesis unfolding sccs_def
    by (auto dest: max_subgraph_prop X intro: induced_subgraphI_arc_mono Y)
qed

locale max_reachable_set = wf_digraph +
  fixes S assumes S_in_sv: "S \<in> sccs_verts"
begin

  lemma reach_in: "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    and not_reach_out: "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
    and not_empty: "S \<noteq> {}"
    using S_in_sv by (auto simp: sccs_verts_def)

  lemma reachable_induced:
    assumes conn: "u \<in> S" "v \<in> S" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v"
  proof -
    let ?H = "G \<restriction> S"
    have "S \<subseteq> verts G" using reach_in by (auto dest: reachable_in_verts)
    then have "induced_subgraph ?H G"
        by (rule induced_induce)
    then interpret H: wf_digraph ?H by (rule wf_digraphI_induced)

    from conn obtain p where p: "awalk u p v" by (metis reachable_awalk)
    show ?thesis
    proof (cases "set p \<subseteq> arcs (G \<restriction> S)")
      case True
      with p conn have "H.awalk u p v"
        by (auto simp: pre_digraph.awalk_def compatible_cas[OF compatible_induce_subgraph])
      then show ?thesis by (metis H.reachable_awalk)
    next
      case False
      then obtain a where "a \<in> set p" "a \<notin> arcs (G \<restriction> S)" by auto
      moreover
      then have "tail G a \<notin> S \<or> head G a \<notin> S" using p by auto
      ultimately
      obtain w where "w \<in> set (awalk_verts u p)" "w \<notin> S" using p by (auto simp: set_awalk_verts)
      then have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
        using p by (auto intro: awalk_verts_reachable_from awalk_verts_reachable_to)
      moreover have "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" using conn reach_in by auto
      ultimately have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" by (auto intro: reachable_trans)
      with \<open>w \<notin> S\<close> conn not_reach_out have False by blast
      then show ?thesis ..
    qed
  qed

  lemma strongly_connected:
    shows "strongly_connected (G \<restriction> S)"
    using not_empty by (intro strongly_connectedI) (auto intro: reachable_induced reach_in)

  lemma induced_in_sccs: "G \<restriction> S \<in> sccs"
  proof -
    let ?H = "G \<restriction> S"
    have "S \<subseteq> verts G" using reach_in by (auto dest: reachable_in_verts)
    then have "induced_subgraph ?H G"
        by (rule induced_induce)
    then interpret H: wf_digraph ?H by (rule wf_digraphI_induced)

    { fix T assume "S \<subset> T" "T \<subseteq> verts G" "strongly_connected (G \<restriction> T)"
      from \<open>S \<subset> T\<close> obtain v where "v \<in> T" "v \<notin> S" by auto
      from not_empty obtain u where "u \<in> S" by auto
      then have "u \<in> T" using \<open>S \<subset> T\<close> by auto

      from \<open>u \<in> S\<close> \<open>v \<notin> S\<close> have "\<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" by (rule not_reach_out)
      moreover
      from \<open>strongly_connected _\<close> have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> u"
        using \<open>v \<in> T\<close> \<open>u \<in> T\<close> by (auto simp: strongly_connected_def)
      then have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
        using \<open>T \<subseteq> verts G\<close> by (auto dest: reachable_induce_subgraphD)
      ultimately have False by blast
    } note psuper_not_sc = this

    have "\<not> (\<exists>c'. induced_subgraph c' G \<and> strongly_connected c' \<and> verts (G \<restriction> S) \<subset> verts c')"
      by (metis induce_subgraph_verts induced_imp_subgraph psuper_not_sc subgraphE
        strongly_connected_imp_induce_subgraph_strongly_connected)
    with \<open>S \<subseteq> _\<close> not_empty show "?H \<in> sccs" by (intro in_sccsI induced_induce strongly_connected)
  qed
end

context wf_digraph begin

  lemma in_verts_sccsD_sccs:
    assumes "S \<in> sccs_verts"
    shows "G \<restriction> S \<in> sccs"
  proof -
    from assms interpret max_reachable_set by unfold_locales
    show ?thesis by (auto simp: sccs_verts_def intro: induced_in_sccs)
  qed

  lemma sccs_verts_conv: "sccs_verts = verts ` sccs"
    by (auto intro: in_sccs_vertsI_sccs rev_image_eqI dest: in_verts_sccsD_sccs)

  lemma induce_eq_iff_induced:
    assumes "induced_subgraph H G" shows "G \<restriction> verts H = H"
    using assms by (auto simp: induced_subgraph_def induce_subgraph_def compatible_def)

  lemma sccs_conv_sccs_verts: "sccs = induce_subgraph G ` sccs_verts"
    by (auto intro!: rev_image_eqI in_sccs_vertsI_sccs dest: in_verts_sccsD_sccs
      simp: sccs_def induce_eq_iff_induced)

end


lemma connected_conv:
  shows "connected G \<longleftrightarrow> verts G \<noteq> {} \<and> (\<forall>u \<in> verts G. \<forall>v \<in> verts G. (u,v) \<in> rtrancl_on (verts G) ((arcs_ends G)\<^sup>s))"
proof -
  have "symcl (arcs_ends G) = parcs (mk_symmetric G)"
    by (auto simp: parcs_mk_symmetric symcl_def arcs_ends_conv)
  then show ?thesis by (auto simp: connected_def strongly_connected_def reachable_def)
qed

lemma (in wf_digraph) symmetric_connected_imp_strongly_connected:
  assumes "symmetric G" "connected G"
  shows "strongly_connected G"
proof
  from \<open>connected G\<close> show "verts G \<noteq> {}" unfolding connected_def strongly_connected_def by auto
next
  from \<open>connected G\<close>
  have sc_mks: "strongly_connected (mk_symmetric G)"
    unfolding connected_def by simp

  fix u v assume "u \<in> verts G" "v \<in> verts G"
  with sc_mks have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
    unfolding strongly_connected_def by auto
  then show "u \<rightarrow>\<^sup>* v" using assms by (simp only: reachable_mk_symmetric_eq)
qed

lemma (in wf_digraph) connected_spanning_imp_connected:
  assumes "spanning H G"
  assumes "connected H"
  shows "connected G"
proof (unfold connected_def strongly_connected_def, intro conjI ballI)
  from assms show "verts (mk_symmetric G )\<noteq> {}"
    unfolding spanning_def connected_def strongly_connected_def by auto
next
  fix u v
  assume "u \<in> verts (mk_symmetric G)" and "v \<in> verts (mk_symmetric G)"
  then have "u \<in> pverts (mk_symmetric H)" and "v \<in> pverts (mk_symmetric H)"
    using \<open>spanning H G\<close> by (auto simp: mk_symmetric_def)
  with \<open>connected H\<close>
  have "u \<rightarrow>\<^sup>*\<^bsub>with_proj (mk_symmetric H)\<^esub> v" "subgraph (mk_symmetric H) (mk_symmetric G)"
    using \<open>spanning H G\<close> unfolding connected_def
    by (auto simp: spanning_def dest: subgraph_mk_symmetric)
  then show "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v" by (rule pre_digraph.reachable_mono)
qed

lemma (in wf_digraph) spanning_tree_imp_connected:
  assumes "spanning_tree H G"
  shows "connected G"
using assms by (auto intro: connected_spanning_imp_connected)

term "LEAST x. P x"

lemma (in sym_digraph) induce_reachable_is_in_sccs:
  assumes "u \<in> verts G"
  shows "(G \<restriction> {v. u \<rightarrow>\<^sup>* v}) \<in> sccs"
proof -
  let ?c = "(G \<restriction> {v. u \<rightarrow>\<^sup>* v})"
  have isub_c: "induced_subgraph ?c G"
    by (auto elim: reachable_in_vertsE)
  then interpret c: wf_digraph ?c by (rule wf_digraphI_induced)

  have sym_c: "symmetric (G \<restriction> {v. u \<rightarrow>\<^sup>* v})"
    using sym_arcs isub_c by (rule induced_graph_imp_symmetric)

  note \<open>induced_subgraph ?c G\<close>
  moreover
  have "strongly_connected ?c"
  proof (rule strongly_connectedI)
    show "verts ?c \<noteq> {}" using assms by auto
  next
    fix v w assume l_assms: "v \<in> verts ?c" "w \<in> verts ?c"
    have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^sup>* v}\<^esub> v"
      using l_assms by (intro induce_reachable_preserves_paths) auto
    then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^sup>* v}\<^esub> u" by (rule symmetric_reachable[OF sym_c])
    also have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^sup>* v}\<^esub> w"
      using l_assms by (intro induce_reachable_preserves_paths) auto
    finally show "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {v. u \<rightarrow>\<^sup>* v}\<^esub> w" .
  qed
  moreover
  have "\<not>(\<exists>d. induced_subgraph d G \<and> strongly_connected d \<and>
    verts ?c \<subset> verts d)"
  proof
    assume "\<exists>d. induced_subgraph d G \<and> strongly_connected d \<and>
      verts ?c \<subset> verts d"
    then obtain d where "induced_subgraph d G" "strongly_connected d"
      "verts ?c \<subset> verts d" by auto
    then obtain v where "v \<in> verts d" and "v \<notin> verts ?c"
      by auto

    have "u \<in> verts ?c" using \<open>u \<in> verts G\<close> by auto
    then have "u \<in> verts d" using \<open>verts ?c \<subset> verts d\<close> by auto 
    then have "u \<rightarrow>\<^sup>*\<^bsub>d\<^esub> v"
      using \<open>strongly_connected d\<close> \<open>u \<in> verts d\<close> \<open>v \<in> verts d\<close> by auto
    then have "u \<rightarrow>\<^sup>* v"
      using \<open>induced_subgraph d G\<close>
      by (auto intro: pre_digraph.reachable_mono)
    then have "v \<in> verts ?c" by (auto simp: reachable_awalk)
    then show False using \<open>v \<notin> verts ?c\<close> by auto
  qed
  ultimately show ?thesis unfolding sccs_def by auto
qed

lemma induced_eq_verts_imp_eq:
  assumes "induced_subgraph G H"
  assumes "induced_subgraph G' H"
  assumes "verts G = verts G'"
  shows "G = G'"
  using assms by (auto simp: induced_subgraph_def subgraph_def compatible_def)

lemma (in pre_digraph) in_sccs_subset_imp_eq:
  assumes "c \<in> sccs"
  assumes "d \<in> sccs"
  assumes "verts c \<subseteq> verts d"
  shows "c = d"
using assms by (blast intro: induced_eq_verts_imp_eq)

context wf_digraph begin

  lemma connectedI:
    assumes "verts G \<noteq> {}" "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
    shows "connected G"
    using assms by (auto simp: connected_def)
  
  lemma connected_awalkE:
    assumes "connected G" "u \<in> verts G" "v \<in> verts G"
    obtains p where "pre_digraph.awalk (mk_symmetric G) u p v"
  proof -
    interpret sG: pair_wf_digraph "mk_symmetric G" ..
    from assms have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v" by (auto simp: connected_def)
    then obtain p where "sG.awalk u p v" by (auto simp: sG.reachable_awalk)
    then show ?thesis ..
  qed

  lemma inj_on_verts_sccs: "inj_on verts sccs"
    by (rule inj_onI) (metis in_sccs_imp_induced induced_eq_verts_imp_eq)

  lemma card_sccs_verts: "card sccs_verts = card sccs"
    by (auto simp: sccs_verts_conv intro: inj_on_verts_sccs card_image)

end


lemma strongly_connected_non_disj:
  assumes wf: "wf_digraph G" "wf_digraph H" "compatible G H"
  assumes sc: "strongly_connected G" "strongly_connected H"
  assumes not_disj: "verts G \<inter> verts H \<noteq> {}"
  shows "strongly_connected (union G H)"
proof
  from sc show "verts (union G H) \<noteq> {}"
    unfolding strongly_connected_def by simp
next
  let ?x = "union G H"
  fix u v w assume "u \<in> verts ?x" and "v \<in> verts ?x"
  obtain w where w_in_both: "w \<in> verts G" "w \<in> verts H"
    using not_disj by auto

  interpret x: wf_digraph ?x
    by (rule wellformed_union) fact+
  have subg: "subgraph G ?x" "subgraph H ?x"
    by (rule subgraphs_of_union[OF _ _ ], fact+)+
  have reach_uw: "u \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> w"
    using \<open>u \<in> verts ?x\<close> subg w_in_both sc
    by (auto intro: pre_digraph.reachable_mono)
  also have reach_wv: "w \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> v"
    using \<open>v \<in> verts ?x\<close> subg w_in_both sc
    by (auto intro: pre_digraph.reachable_mono)
  finally (x.reachable_trans) show "u \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> v" .
qed

context wf_digraph begin

  lemma scc_disj:
    assumes scc: "c \<in> sccs" "d \<in> sccs"
    assumes "c \<noteq> d"
    shows "verts c \<inter> verts d = {}"
  proof (rule ccontr)
    assume contr: "\<not>?thesis"

    let ?x = "union c d"

    have comp1: "compatible G c" "compatible G d"
      using scc by (auto simp: sccs_def)
    then have comp: "compatible c d" by (auto simp: compatible_def)

    have wf: "wf_digraph c" "wf_digraph d"
      and sc: "strongly_connected c" "strongly_connected d"
      using scc by (auto intro: in_sccs_imp_induced)
    have "compatible c d"
      using comp by (auto simp: sccs_def compatible_def)
    from wf comp sc have union_conn: "strongly_connected ?x"
      using contr by (rule strongly_connected_non_disj)

    have sg: "subgraph ?x G"
      using scc comp1 by (intro subgraph_union) (auto simp: compatible_def)
    then have v_cd: "verts c \<subseteq> verts G"  "verts d \<subseteq> verts G" by (auto elim!: subgraphE)
    have "wf_digraph ?x" by (rule wellformed_union) fact+
    with v_cd sg union_conn
    have induce_subgraph_conn: "strongly_connected (G \<restriction> verts ?x)"
        "induced_subgraph (G \<restriction> verts ?x) G"
      by - (intro strongly_connected_imp_induce_subgraph_strongly_connected,
        auto simp: subgraph_union_iff)

    from assms have "\<not>verts c \<subseteq> verts d" and "\<not> verts d \<subseteq> verts c"
      by (metis in_sccs_subset_imp_eq)+
    then have psub: "verts c \<subset> verts ?x"
      by (auto simp: union_def)
    then show False using induce_subgraph_conn
      by (metis \<open>c \<in> sccs\<close> in_sccsE induce_subgraph_verts)
  qed

  lemma in_sccs_verts_conv:
    "S \<in> sccs_verts \<longleftrightarrow> G \<restriction> S \<in> sccs"
    by (auto simp: sccs_verts_conv intro: rev_image_eqI)
      (metis in_sccs_imp_induced induce_subgraph_verts induced_eq_verts_imp_eq induced_imp_subgraph induced_induce subgraphE)

end

lemma (in wf_digraph) in_scc_of_self: "u \<in> verts G \<Longrightarrow> u \<in> scc_of u"
  by (auto simp: scc_of_def)

lemma (in wf_digraph) scc_of_empty_conv: "scc_of u = {} \<longleftrightarrow> u \<notin> verts G"
  using in_scc_of_self by (auto simp: scc_of_def reachable_in_verts)

lemma (in wf_digraph) scc_of_in_sccs_verts:
  assumes "u \<in> verts G" shows "scc_of u \<in> sccs_verts"
  using assms by (auto simp: in_sccs_verts_conv_reachable scc_of_def intro: reachable_trans exI[where x=u])

lemma (in wf_digraph) sccs_verts_subsets: "S \<in> sccs_verts \<Longrightarrow> S \<subseteq> verts G"
  by (auto simp: sccs_verts_conv)

lemma (in fin_digraph) finite_sccs_verts: "finite sccs_verts"
proof -
  have "finite (Pow (verts G))" by auto
  moreover with sccs_verts_subsets have "sccs_verts \<subseteq> Pow (verts G)" by auto
  ultimately show ?thesis by (rule rev_finite_subset)
qed

lemma (in wf_digraph) sccs_verts_conv_scc_of:
  "sccs_verts = scc_of ` verts G" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix S assume "S \<in> ?R" then show "S \<in> ?L"
    by (auto simp: in_sccs_verts_conv_reachable scc_of_empty_conv) (auto simp: scc_of_def intro: reachable_trans)
next
  fix S assume "S \<in> ?L"
  moreover
  then obtain u where "u \<in> S" by (auto simp: in_sccs_verts_conv_reachable)
  moreover
  then have "u \<in> verts G" using \<open>S \<in> ?L\<close> by (metis sccs_verts_subsets subsetCE)
  then have "scc_of u \<in> sccs_verts" "u \<in> scc_of u"
    by (auto intro: scc_of_in_sccs_verts in_scc_of_self)
  ultimately
  have "scc_of u = S" using sccs_verts_disjoint by blast
  then show "S \<in> ?R" using \<open>scc_of u \<in> _\<close> \<open>u \<in> verts G\<close> by auto
qed

lemma (in sym_digraph) scc_ofI_reachable:
  assumes "u \<rightarrow>\<^sup>* v" shows "u \<in> scc_of v"
  using assms by (auto simp: scc_of_def symmetric_reachable[OF sym_arcs])

lemma (in sym_digraph) scc_ofI_reachable':
  assumes "v \<rightarrow>\<^sup>* u" shows "u \<in> scc_of v"
  using assms by (auto simp: scc_of_def symmetric_reachable[OF sym_arcs])

lemma (in sym_digraph) scc_ofI_awalk:
  assumes "awalk u p v" shows "u \<in> scc_of v"
  using assms by (metis reachable_awalk scc_ofI_reachable)

lemma (in sym_digraph) scc_ofI_apath:
  assumes "apath u p v" shows "u \<in> scc_of v"
  using assms by (metis reachable_apath scc_ofI_reachable)

lemma (in wf_digraph) scc_of_eq: "u \<in> scc_of v \<Longrightarrow> scc_of u = scc_of v"
  by (auto simp: scc_of_def intro: reachable_trans)

lemma (in wf_digraph) strongly_connected_eq_iff:
  "strongly_connected G \<longleftrightarrow> sccs = {G}" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have "G \<in> sccs" by (auto simp: sccs_def induced_subgraph_refl)
  moreover
  { fix H assume "H \<in> sccs" "G \<noteq> H"
    with \<open>G \<in> sccs\<close> have "verts G \<inter> verts H = {}" by (rule scc_disj)
    moreover
    from \<open>H \<in> sccs\<close> have "verts H \<subseteq> verts G" by auto
    ultimately
    have "verts H = {}" by auto
    with \<open>H \<in> sccs\<close> have "False" by (auto simp: sccs_def strongly_connected_def)
  } ultimately
  show ?R by auto
qed (auto simp: sccs_def)




subsection \<open>Components\<close>

lemma (in sym_digraph) exists_scc:
  assumes "verts G \<noteq> {}" shows "\<exists>c. c \<in> sccs"
proof -
  from assms obtain u where "u \<in> verts G" by auto
  then show ?thesis by (blast dest: induce_reachable_is_in_sccs)
qed

theorem (in sym_digraph) graph_is_union_sccs:
  shows "Union sccs = G"
proof -
  have "(\<Union>c \<in> sccs. verts c) = verts G"
    by (auto intro: induce_reachable_is_in_sccs)
  moreover
  have "(\<Union>c \<in> sccs. arcs c) = arcs G"
  proof
    show "(\<Union>c \<in> sccs. arcs c) \<subseteq> arcs G"
      by safe (metis in_sccsE induced_imp_subgraph subgraphE subsetD)
    show "arcs G \<subseteq> (\<Union>c \<in> sccs. arcs c)"
    proof (safe)
      fix e assume "e \<in> arcs G"
      define a b where [simp]: "a = tail G e" and [simp]: "b = head G e"

      have "e \<in> (\<Union>x \<in> sccs. arcs x)"
      proof cases
        assume "\<exists>x\<in>sccs. {a,b } \<subseteq> verts x"
        then obtain c where "c \<in> sccs" and "{a,b} \<subseteq> verts c"
          by auto
        then have "e \<in> {e \<in> arcs G. tail G e \<in> verts c
          \<and> head G e \<in> verts c}" using \<open>e \<in> arcs G\<close> by auto
        then have "e \<in> arcs c" using \<open>c \<in> sccs\<close> by blast
        then show ?thesis using \<open>c \<in> sccs\<close> by auto
      next
        assume l_assm: "\<not>(\<exists>x\<in>sccs. {a,b} \<subseteq> verts x)"

        have "a \<rightarrow>\<^sup>* b" using \<open>e \<in> arcs G\<close> 
          by (metis a_def b_def reachable_adjI in_arcs_imp_in_arcs_ends)
        then have "{a,b} \<subseteq> verts (G \<restriction> {v. a \<rightarrow>\<^sup>* v})" "a \<in> verts G"
          by (auto elim: reachable_in_vertsE)
        moreover
        have "(G \<restriction> {v. a \<rightarrow>\<^sup>* v}) \<in> sccs"
          using \<open>a \<in> verts G\<close> by (auto intro: induce_reachable_is_in_sccs)
        ultimately
        have False using l_assm by blast
        then show ?thesis by simp
      qed
      then show "e \<in> (\<Union>c \<in> sccs. arcs c)" by auto
    qed
  qed
  ultimately show ?thesis
    by (auto simp add: Union_def)
qed

lemma (in sym_digraph) scc_for_vert_ex:
  assumes "u \<in> verts G"
  shows "\<exists>c. c\<in>sccs \<and> u \<in> verts c"
using assms by (auto intro: induce_reachable_is_in_sccs)



lemma (in sym_digraph) scc_decomp_unique:
  assumes "S \<subseteq> sccs" "verts (Union S) = verts G" shows "S = sccs"
proof (rule ccontr)
  assume "S \<noteq> sccs"
  with assms obtain c where "c \<in> sccs" and "c \<notin> S" by auto
  with assms have "\<And>d. d \<in> S \<Longrightarrow> verts c \<inter> verts d = {}"
    by (intro scc_disj) auto
  then have "verts c \<inter> verts (Union S) = {}"
    by (auto simp: Union_def)
  with assms have "verts c \<inter> verts G = {}" by auto
  moreover from \<open>c \<in> sccs\<close> obtain u where "u \<in> verts c \<inter> verts G"
    by (auto simp: sccs_def strongly_connected_def)
  ultimately show False by blast
qed


end
