(* Title:  Digraph.thy
   Author: Lars Noschinski, TU München
   Author: René Neumann
*)

theory Digraph
imports
  Main
  Rtrancl_On
  Stuff
begin

section \<open>Digraphs\<close>

record ('a,'b) pre_digraph =
  verts :: "'a set"
  arcs :: "'b set"
  tail :: "'b \<Rightarrow> 'a"
  head :: "'b \<Rightarrow> 'a"

definition arc_to_ends :: "('a,'b) pre_digraph \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'a" where
  "arc_to_ends G e \<equiv> (tail G e, head G e)"

locale pre_digraph =
  fixes G :: "('a, 'b) pre_digraph" (structure)

locale wf_digraph = pre_digraph +
  assumes tail_in_verts[simp]: "e \<in> arcs G \<Longrightarrow> tail G e \<in> verts G"
  assumes head_in_verts[simp]: "e \<in> arcs G \<Longrightarrow> head G e \<in> verts G"
begin

lemma wf_digraph: "wf_digraph G" by intro_locales

lemmas wellformed = tail_in_verts head_in_verts

end

definition arcs_ends :: "('a,'b) pre_digraph \<Rightarrow> ('a \<times> 'a) set" where
  "arcs_ends G \<equiv> arc_to_ends G ` arcs G"

definition symmetric :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "symmetric G \<equiv> sym (arcs_ends G)"

text \<open>
  Matches "pseudo digraphs" from \cite{bangjensen2009digraphs}, except for
  allowing the null graph. For a discussion of that topic,
  see also \cite{harary1974nullgraph}.
\<close>
locale fin_digraph = wf_digraph +
  assumes finite_verts[simp]: "finite (verts G)"
    and finite_arcs[simp]: "finite (arcs G)"

locale loopfree_digraph = wf_digraph +
  assumes no_loops: "e \<in> arcs G \<Longrightarrow> tail G e \<noteq> head G e"

locale nomulti_digraph = wf_digraph +
  assumes no_multi_arcs: "\<And>e1 e2. \<lbrakk>e1 \<in> arcs G; e2 \<in> arcs G;
     arc_to_ends G e1 = arc_to_ends G e2\<rbrakk> \<Longrightarrow> e1 = e2"

locale sym_digraph = wf_digraph +
  assumes sym_arcs[intro]: "symmetric G"

locale digraph = fin_digraph + loopfree_digraph + nomulti_digraph

text \<open>
  We model graphs as symmetric digraphs. This is fine for many purposes,
  but not for all. For example, the path $a,b,a$ is considered to be a cycle
  in a digraph (and hence in a symmetric digraph), but not in an undirected
  graph.
\<close>
locale pseudo_graph = fin_digraph + sym_digraph

locale graph = digraph + pseudo_graph

lemma (in wf_digraph) fin_digraphI[intro]:
  assumes "finite (verts G)"
  assumes "finite (arcs G)"
  shows "fin_digraph G"
using assms by unfold_locales

lemma (in wf_digraph) sym_digraphI[intro]:
  assumes "symmetric G"
  shows "sym_digraph G"
using assms by unfold_locales

lemma (in digraph) graphI[intro]:
  assumes "symmetric G"
  shows "graph G"
using assms by unfold_locales



definition (in wf_digraph) arc :: "'b \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "arc e uv \<equiv> e \<in> arcs G \<and> tail G e = fst uv \<and> head G e = snd uv"


lemma (in fin_digraph) fin_digraph: "fin_digraph G"
  by unfold_locales

lemma (in nomulti_digraph) nomulti_digraph: "nomulti_digraph G" by unfold_locales

lemma arcs_ends_conv: "arcs_ends G = (\<lambda>e. (tail G e, head G e)) ` arcs G"
  by (auto simp: arc_to_ends_def arcs_ends_def)

lemma symmetric_conv: "symmetric G \<longleftrightarrow> (\<forall>e1 \<in> arcs G. \<exists>e2 \<in> arcs G. tail G e1 = head G e2 \<and> head G e1 = tail G e2)"
  unfolding symmetric_def arcs_ends_conv sym_def by auto

lemma arcs_ends_symmetric:
  assumes "symmetric G"
  shows "(u,v) \<in> arcs_ends G \<Longrightarrow> (v,u) \<in> arcs_ends G"
  using assms unfolding symmetric_def sym_def by auto

lemma (in nomulti_digraph) inj_on_arc_to_ends:
  "inj_on (arc_to_ends G) (arcs G)"
  by (rule inj_onI) (rule no_multi_arcs)



subsection \<open>Reachability\<close>

abbreviation dominates :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<index> _" [100,100] 40) where
  "dominates G u v \<equiv> (u,v) \<in> arcs_ends G"

abbreviation reachable1 :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>+\<index> _" [100,100] 40) where
  "reachable1 G u v \<equiv> (u,v) \<in> (arcs_ends G)^+"

definition reachable :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>*\<index> _" [100,100] 40) where
  "reachable G u v \<equiv> (u,v) \<in> rtrancl_on (verts G) (arcs_ends G)"

lemma reachableE[elim]:
  assumes "u \<rightarrow>\<^bsub>G\<^esub> v"
  obtains e where "e \<in> arcs G" "tail G e = u" "head G e = v"
using assms by (auto simp add: arcs_ends_conv)

lemma (in loopfree_digraph) adj_not_same:
  assumes "a \<rightarrow> a" shows "False"
  using assms by (rule reachableE) (auto dest: no_loops)

lemma reachable_in_vertsE:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" obtains "u \<in> verts G" "v \<in> verts G"
  using assms unfolding reachable_def by induct auto

lemma symmetric_reachable:
  assumes "symmetric G" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" shows "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
proof -
  have "sym (rtrancl_on (verts G) (arcs_ends G))"
    using assms by (auto simp add: symmetric_def dest: rtrancl_on_sym)
  then show ?thesis using assms unfolding reachable_def by (blast elim: symE)
qed

lemma reachable_rtranclI:
  "u \<rightarrow>\<^sup>*\<^bsub>G \<^esub> v \<Longrightarrow> (u, v) \<in> (arcs_ends G)\<^sup>*"
  unfolding reachable_def by (rule rtrancl_on_rtranclI)


context wf_digraph begin

lemma adj_in_verts:
  assumes "u \<rightarrow>\<^bsub>G\<^esub> v" shows "u \<in> verts G" "v \<in> verts G"
  using assms unfolding arcs_ends_conv by auto

lemma dominatesI: assumes "arc_to_ends G a = (u,v)" "a \<in> arcs G" shows "u \<rightarrow>\<^bsub>G\<^esub> v"
  using assms by (auto simp: arcs_ends_def intro: rev_image_eqI)

lemma reachable_refl [intro!, Pure.intro!, simp]: "v \<in> verts G \<Longrightarrow> v \<rightarrow>\<^sup>* v"
  unfolding reachable_def by auto

lemma adj_reachable_trans[trans]:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "b \<rightarrow>\<^sup>*\<^bsub>G\<^esub> c" shows "a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> c"
  using assms by (auto simp: reachable_def intro: converse_rtrancl_on_into_rtrancl_on adj_in_verts)

lemma reachable_adj_trans[trans]:
  assumes "a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> b" "b \<rightarrow>\<^bsub>G\<^esub> c" shows "a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> c"
  using assms by (auto simp: reachable_def intro: rtrancl_on_into_rtrancl_on adj_in_verts)

lemma reachable_adjI [intro, simp]: "u \<rightarrow> v \<Longrightarrow> u \<rightarrow>\<^sup>* v"
  by (auto intro: adj_reachable_trans adj_in_verts)

lemma reachable_trans[trans]:
  assumes "u \<rightarrow>\<^sup>*v" "v \<rightarrow>\<^sup>* w" shows "u \<rightarrow>\<^sup>* w"
  using assms unfolding reachable_def by (rule rtrancl_on_trans)

lemma reachable_induct[consumes 1, case_names base step]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    and cases: "u \<in> verts G \<Longrightarrow> P u"
       "\<And>x y. \<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x; x \<rightarrow>\<^bsub>G\<^esub> y; P x\<rbrakk> \<Longrightarrow> P y"
  shows "P v"
  using assms unfolding reachable_def by (rule rtrancl_on_induct) auto

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    and cases: "v \<in> verts G \<Longrightarrow> P v"
       "\<And>x y. \<lbrakk>x \<rightarrow>\<^bsub>G\<^esub> y; y \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
  shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct) auto

lemma (in pre_digraph) converse_reachable_cases:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  obtains (base) "u = v" "u \<in> verts G"
    | (step) w where "u \<rightarrow>\<^bsub>G\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms unfolding reachable_def by (cases rule: converse_rtrancl_on_cases) auto

lemma reachable_in_verts:
  assumes "u \<rightarrow>\<^sup>* v" shows "u \<in> verts G" "v \<in> verts G"
  using assms by induct (simp_all add: adj_in_verts)

lemma reachable1_in_verts:
  assumes "u \<rightarrow>\<^sup>+ v" shows "u \<in> verts G" "v \<in> verts G"
  using assms
  by induct (simp_all add: adj_in_verts)

lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^sup>+ w \<Longrightarrow> v \<rightarrow>\<^sup>* w"
  unfolding reachable_def
  by (rule rtrancl_consistent_rtrancl_on) (simp_all add: reachable1_in_verts adj_in_verts)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^sup>* w"
  and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^sup>+ w"
proof -
  from reach have "(v,w) \<in> (arcs_ends G)^*" by (rule reachable_rtranclI)
  with neq show ?thesis by (auto dest: rtranclD)
qed

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

lemma reachable1_reachable_trans [trans]:
  "u \<rightarrow>\<^sup>+ v \<Longrightarrow> v \<rightarrow>\<^sup>* w \<Longrightarrow> u \<rightarrow>\<^sup>+ w"
by (metis trancl_trans reachable_neq_reachable1)

lemma reachable_reachable1_trans [trans]:
  "u \<rightarrow>\<^sup>* v \<Longrightarrow> v \<rightarrow>\<^sup>+ w \<Longrightarrow> u \<rightarrow>\<^sup>+ w"
by (metis trancl_trans reachable_neq_reachable1)

lemma reachable_conv:
  "u \<rightarrow>\<^sup>* v \<longleftrightarrow> (u,v) \<in> (arcs_ends G)^* \<inter> (verts G \<times> verts G)"
  apply (auto intro: reachable_in_verts)
  apply (induct rule: rtrancl_induct)
   apply auto
  done

lemma reachable_conv':
  assumes "u \<in> verts G"
  shows "u \<rightarrow>\<^sup>* v \<longleftrightarrow> (u,v) \<in> (arcs_ends G)\<^sup>*" (is "?L = ?R")
proof
  assume "?R" then show "?L" using assms  by induct auto
qed (auto simp: reachable_conv)


end

lemma (in sym_digraph) symmetric_reachable':
  assumes "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" shows "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using sym_arcs assms by (rule symmetric_reachable)




subsection \<open>Degrees of vertices\<close>

definition in_arcs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "in_arcs G v \<equiv> {e \<in> arcs G. head G e = v}"

definition out_arcs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "out_arcs G v \<equiv> {e \<in> arcs G. tail G e = v}"

definition in_degree :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> nat" where
  "in_degree G v \<equiv> card (in_arcs G v)"

definition out_degree :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> nat" where
  "out_degree G v \<equiv> card (out_arcs G v)"

lemma (in fin_digraph) finite_in_arcs[intro]:
  "finite (in_arcs G v)"
  unfolding in_arcs_def by auto

lemma (in fin_digraph) finite_out_arcs[intro]:
  "finite (out_arcs G v)"
  unfolding out_arcs_def by auto

lemma in_in_arcs_conv[simp]:
  "e \<in> in_arcs G v \<longleftrightarrow> e \<in> arcs G \<and> head G e = v"
  unfolding in_arcs_def by auto

lemma in_out_arcs_conv[simp]:
  "e \<in> out_arcs G v \<longleftrightarrow> e \<in> arcs G \<and> tail G e = v"
  unfolding out_arcs_def by auto

lemma inout_arcs_arc_simps[simp]:
  assumes "e \<in> arcs G"
  shows "tail G e = u \<Longrightarrow> out_arcs G u \<inter> insert e E = insert e (out_arcs G u \<inter> E)"
        "tail G e \<noteq> u \<Longrightarrow> out_arcs G u \<inter> insert e E = out_arcs G u \<inter> E"
        "out_arcs G u \<inter> {} = {}" (* XXX: should be unnecessary *)
        "head G e = u \<Longrightarrow> in_arcs G u \<inter> insert e E = insert e (in_arcs G u \<inter> E)"
        "head G e \<noteq> u \<Longrightarrow> in_arcs G u \<inter> insert e E = in_arcs G u \<inter> E"
        "in_arcs G u \<inter> {} = {}" (* XXX: should be unnecessary *)
  using assms by auto

lemma in_arcs_int_arcs[simp]: "in_arcs G u \<inter> arcs G = in_arcs G u" and
      out_arcs_int_arcs[simp]: "out_arcs G u \<inter> arcs G = out_arcs G u"
  by auto


lemma in_arcs_in_arcs: "x \<in> in_arcs G u \<Longrightarrow> x \<in> arcs G"
  and out_arcs_in_arcs: "x \<in> out_arcs G u \<Longrightarrow> x \<in> arcs G"
  by (auto simp: in_arcs_def out_arcs_def)



subsection \<open>Graph operations\<close>

context pre_digraph begin

definition add_arc :: "'b \<Rightarrow>  ('a,'b) pre_digraph" where
  "add_arc a = \<lparr> verts = verts G \<union> {tail G a, head G a}, arcs = insert a (arcs G), tail = tail G, head = head G \<rparr>"

definition  del_arc :: "'b \<Rightarrow> ('a,'b) pre_digraph" where
  "del_arc a = \<lparr> verts = verts G, arcs = arcs G - {a}, tail = tail G, head = head G \<rparr>"

definition add_vert :: "'a \<Rightarrow>  ('a,'b) pre_digraph" where
  "add_vert v = \<lparr> verts = insert v (verts G), arcs = arcs G, tail = tail G, head = head G \<rparr>"

definition del_vert :: "'a \<Rightarrow>  ('a,'b) pre_digraph" where
  "del_vert v = \<lparr> verts = verts G - {v}, arcs = {a \<in> arcs G. tail G a \<noteq> v \<and> head G a \<noteq> v}, tail = tail G, head = head G \<rparr>"

lemma
  verts_add_arc: "\<lbrakk> tail G a \<in> verts G; head G a \<in> verts G \<rbrakk> \<Longrightarrow> verts (add_arc a) = verts G"  and
  verts_add_arc_conv: "verts (add_arc a) = verts G \<union> {tail G a, head G a}" and
  arcs_add_arc: "arcs (add_arc a) = insert a (arcs G)" and
  tail_add_arc: "tail (add_arc a) = tail G" and
  head_add_arc: "head (add_arc a) = head G"
  by (auto simp: add_arc_def)

lemmas add_arc_simps[simp] = verts_add_arc arcs_add_arc tail_add_arc head_add_arc

lemma
  verts_del_arc: "verts (del_arc a) = verts G"  and
  arcs_del_arc: "arcs (del_arc a) = arcs G - {a}" and
  tail_del_arc: "tail (del_arc a) = tail G" and
  head_del_arc: "head (del_arc a) = head G"
  by (auto simp: del_arc_def)

lemmas del_arc_simps[simp] = verts_del_arc arcs_del_arc tail_del_arc head_del_arc

lemma
    verts_add_vert: "verts (pre_digraph.add_vert G u) = insert u (verts G)" and
    arcs_add_vert: "arcs (pre_digraph.add_vert G u) = arcs G" and
    tail_add_vert: "tail (pre_digraph.add_vert G u) = tail G" and
    head_add_vert: "head (pre_digraph.add_vert G u) = head G"
  by (auto simp: pre_digraph.add_vert_def)

lemmas add_vert_simps = verts_add_vert arcs_add_vert tail_add_vert head_add_vert

lemma
    verts_del_vert: "verts (pre_digraph.del_vert G u) = verts G - {u}" and
    arcs_del_vert: "arcs (pre_digraph.del_vert G u) = {a \<in> arcs G. tail G a \<noteq> u \<and> head G a \<noteq> u}" and
    tail_del_vert: "tail (pre_digraph.del_vert G u) = tail G" and
    head_del_vert: "head (pre_digraph.del_vert G u) = head G" and
    ends_del_vert: "arc_to_ends (pre_digraph.del_vert G u) = arc_to_ends G"
  by (auto simp: pre_digraph.del_vert_def arc_to_ends_def)

lemmas del_vert_simps = verts_del_vert arcs_del_vert tail_del_vert head_del_vert

lemma add_add_arc_collapse[simp]: "pre_digraph.add_arc (add_arc a) a = add_arc a"
  by (auto simp: pre_digraph.add_arc_def)

lemma add_del_arc_collapse[simp]: "pre_digraph.add_arc (del_arc a) a = add_arc a"
  by (auto simp: pre_digraph.verts_add_arc_conv pre_digraph.add_arc_simps)

lemma del_add_arc_collapse[simp]:
  "\<lbrakk> tail G a \<in> verts G; head G a \<in> verts G \<rbrakk> \<Longrightarrow> pre_digraph.del_arc (add_arc a) a = del_arc a"
  by (auto simp: pre_digraph.add_arc_simps pre_digraph.del_arc_simps)

lemma del_del_arc_collapse[simp]: "pre_digraph.del_arc (del_arc a) a = del_arc a"
  by (auto simp: pre_digraph.add_arc_simps pre_digraph.del_arc_simps)

lemma add_arc_commute: "pre_digraph.add_arc (add_arc b) a = pre_digraph.add_arc (add_arc a) b"
  by (auto simp: pre_digraph.add_arc_def)

lemma del_arc_commute: "pre_digraph.del_arc (del_arc b) a = pre_digraph.del_arc (del_arc a) b"
  by (auto simp: pre_digraph.del_arc_def)

lemma del_arc_in: "a \<notin> arcs G \<Longrightarrow> del_arc a = G"
  by (rule pre_digraph.equality) (auto simp: add_arc_def)

lemma in_arcs_add_arc_iff:
  "in_arcs (add_arc a) u = (if head G a = u then insert a (in_arcs G u) else in_arcs G u)"
  by auto

lemma out_arcs_add_arc_iff:
  "out_arcs (add_arc a) u = (if tail G a = u then insert a (out_arcs G u) else out_arcs G u)"
  by auto

lemma in_arcs_del_arc_iff:
  "in_arcs (del_arc a) u = (if head G a = u then in_arcs G u - {a} else in_arcs G u)"
  by auto

lemma out_arcs_del_arc_iff:
  "out_arcs (del_arc a) u = (if tail G a = u then out_arcs G u - {a} else out_arcs G u)"
  by auto

lemma (in wf_digraph) add_arc_in: "a \<in> arcs G \<Longrightarrow> add_arc a = G"
  by (rule pre_digraph.equality) (auto simp: add_arc_def)

end



context wf_digraph begin

lemma wf_digraph_add_arc[intro]:
  "wf_digraph (add_arc a)" by unfold_locales (auto simp: verts_add_arc_conv)

lemma wf_digraph_del_arc[intro]:
  "wf_digraph (del_arc a)" by unfold_locales (auto simp: verts_add_arc_conv)

lemma wf_digraph_del_vert: "wf_digraph (del_vert u)"
  by standard (auto simp: del_vert_simps)

lemma wf_digraph_add_vert: "wf_digraph (add_vert u)"
  by standard (auto simp: add_vert_simps)

lemma del_vert_add_vert:
  assumes "u \<notin> verts G"
  shows "pre_digraph.del_vert (add_vert u) u = G"
  using assms by (intro pre_digraph.equality) (auto simp: pre_digraph.del_vert_def add_vert_def)

end


context fin_digraph begin

lemma in_degree_add_arc_iff:
  "in_degree (add_arc a) u = (if head G a = u \<and> a \<notin> arcs G then in_degree G u + 1 else in_degree G u)"
proof -
  have "a \<notin> arcs G \<Longrightarrow> a \<notin> in_arcs G u" by (auto simp: in_arcs_def)
  with finite_in_arcs show ?thesis
    unfolding in_degree_def by (auto simp: in_arcs_add_arc_iff intro: arg_cong[where f=card])
qed

lemma out_degree_add_arc_iff:
  "out_degree (add_arc a) u = (if tail G a = u \<and> a \<notin> arcs G then out_degree G u + 1 else out_degree G u)"
proof -
  have "a \<notin> arcs G \<Longrightarrow> a \<notin> out_arcs G u" by (auto simp: out_arcs_def)
  with finite_out_arcs show ?thesis
    unfolding out_degree_def by (auto simp: out_arcs_add_arc_iff intro: arg_cong[where f=card])
qed

lemma in_degree_del_arc_iff:
  "in_degree (del_arc a) u = (if head G a = u \<and> a \<in> arcs G then in_degree G u - 1 else in_degree G u)"
proof -
  have "a \<notin> arcs G \<Longrightarrow> a \<notin> in_arcs G u" by (auto simp: in_arcs_def)
  with finite_in_arcs show ?thesis
    unfolding in_degree_def by (auto simp: in_arcs_del_arc_iff intro: arg_cong[where f=card])
qed

lemma out_degree_del_arc_iff:
  "out_degree (del_arc a) u = (if tail G a = u \<and> a \<in> arcs G then out_degree G u - 1 else out_degree G u)"
proof -
  have "a \<notin> arcs G \<Longrightarrow> a \<notin> out_arcs G u" by (auto simp: out_arcs_def)
  with finite_out_arcs show ?thesis
    unfolding out_degree_def by (auto simp: out_arcs_del_arc_iff intro: arg_cong[where f=card])
qed

lemma fin_digraph_del_vert: "fin_digraph (del_vert u)"
  by standard (auto simp: del_vert_simps)

lemma fin_digraph_del_arc: "fin_digraph (del_arc a)"
  by standard (auto simp: del_vert_simps)

end

end
