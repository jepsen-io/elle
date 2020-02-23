(*  Title:  Kuratowski.thy
    Author: Lars Noschinski, TU München
*)

theory Kuratowski
imports
  Arc_Walk
  Digraph_Component
  Subdivision
  "HOL-Library.Rewrite"
begin

section \<open>Kuratowski Subgraphs\<close>

text \<open>
  We consider the underlying undirected graphs. The underlying undirected graph is represented as a
  symmetric digraph.
\<close>

subsection \<open>Public definitions\<close>

definition complete_digraph :: "nat \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" ("K\<^bsub>_\<^esub>") where
  "complete_digraph n G \<equiv> graph G \<and> card (verts G) = n \<and> arcs_ends G = {(u,v). (u,v) \<in> verts G \<times> verts G \<and> u \<noteq> v}"

definition complete_bipartite_digraph :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) pre_digraph \<Rightarrow> bool" ("K\<^bsub>_,_\<^esub>") where
  "complete_bipartite_digraph m n G \<equiv> graph G \<and> (\<exists>U V. verts G = U \<union> V \<and> U \<inter> V = {}
    \<and> card U = m \<and> card V = n \<and> arcs_ends G = U \<times> V \<union> V \<times> U)"

definition kuratowski_planar :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "kuratowski_planar G \<equiv> \<not>(\<exists>H. subgraph H G \<and> (\<exists>K rev_K rev_H. subdivision (K, rev_K) (H, rev_H) \<and> (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K)))"

lemma complete_digraph_pair_def: "K\<^bsub>n\<^esub> (with_proj G)
  \<longleftrightarrow> finite (pverts G) \<and> card (pverts G) = n \<and> parcs G = {(u,v). (u,v) \<in> (pverts G \<times> pverts G) \<and> u \<noteq> v}" (is "_ = ?R")
proof
  assume A: "K\<^bsub>n\<^esub> G"
  then interpret graph "with_proj G" by (simp add: complete_digraph_def)
  show ?R using A finite_verts by (auto simp: complete_digraph_def)
next
  assume A: ?R
  moreover
  then have "finite (pverts G \<times> pverts G)" "parcs G \<subseteq> pverts G \<times> pverts G"
    by auto
  then have "finite (parcs G)" by (rule rev_finite_subset)
  ultimately interpret pair_graph G
    by unfold_locales (auto simp:  symmetric_def split: prod.splits intro: symI)
  show "K\<^bsub>n\<^esub> G" using A finite_verts by (auto simp: complete_digraph_def)
qed

lemma complete_bipartite_digraph_pair_def: "K\<^bsub>m,n\<^esub> (with_proj G) \<longleftrightarrow> finite (pverts G)
    \<and> (\<exists>U V. pverts G = U \<union> V \<and> U \<inter> V = {} \<and> card U = m \<and> card V = n \<and> parcs G = U \<times> V \<union> V \<times> U)" (is "_ = ?R")
proof
  assume A: "K\<^bsub>m,n\<^esub> G"
  then interpret graph G by (simp add: complete_bipartite_digraph_def)
  show ?R using A finite_verts by (auto simp: complete_bipartite_digraph_def)
next
  assume A: ?R
  then interpret pair_graph G
    by unfold_locales (fastforce simp: complete_bipartite_digraph_def symmetric_def split: prod.splits intro: symI)+
  show "K\<^bsub>m,n\<^esub> G" using A by (auto simp: complete_bipartite_digraph_def)
qed

lemma pair_graphI_complete:
  assumes "K\<^bsub>n\<^esub> (with_proj G)"
  shows "pair_graph G"
proof -
  from assms interpret graph "with_proj G" by (simp add: complete_digraph_def)
  show "pair_graph G"
    using finite_arcs finite_verts sym_arcs wellformed no_loops by unfold_locales simp_all
qed

lemma pair_graphI_complete_bipartite:
  assumes "K\<^bsub>m,n\<^esub> (with_proj G)"
  shows "pair_graph G"
proof -
  from assms interpret graph "with_proj G" by (simp add: complete_bipartite_digraph_def)
  show "pair_graph G"
    using finite_arcs finite_verts sym_arcs wellformed no_loops by unfold_locales simp_all
qed



subsection \<open>Inner vertices of a walk\<close>

context pre_digraph begin

definition (in pre_digraph) inner_verts :: "'b awalk \<Rightarrow> 'a list" where
  "inner_verts p \<equiv> tl (map (tail G) p)"

lemma inner_verts_Nil[simp]: "inner_verts [] = []" by (auto simp: inner_verts_def)

lemma inner_verts_singleton[simp]: "inner_verts [x] = []" by (auto simp: inner_verts_def)

lemma (in wf_digraph) inner_verts_Cons:
  assumes "awalk u (e # es) v"
  shows "inner_verts (e # es) = (if es \<noteq> [] then head G e # inner_verts es else [])"
  using assms by (induct es) (auto simp: inner_verts_def)

lemma (in - ) inner_verts_with_proj_def:
  "pre_digraph.inner_verts (with_proj G) p = tl (map fst p)"
  unfolding pre_digraph.inner_verts_def by simp

lemma inner_verts_conv: "inner_verts p = butlast (tl (awalk_verts u p))"
  unfolding inner_verts_def awalk_verts_conv by simp

lemma (in pre_digraph) inner_verts_empty[simp]:
  assumes "length p < 2" shows "inner_verts p = []"
  using assms by (cases p) (auto simp: inner_verts_def)

lemma (in wf_digraph) set_inner_verts:
  assumes "apath u p v"
  shows "set (inner_verts p) = set (awalk_verts u p) - {u,v}"
proof (cases "length p < 2")
  case True with assms show ?thesis
    by (cases p) (auto simp: inner_verts_conv[of _ u] apath_def)
next
  case False
  have "awalk_verts u p = u # inner_verts p @ [v]"
    using assms False length_awalk_verts[of u p] inner_verts_conv[of p u]
    by (cases "awalk_verts u p") (auto simp: apath_def awalk_conv)
  then show ?thesis using assms by (auto simp: apath_def)
qed

lemma in_set_inner_verts_appendI_l:
  assumes "u \<in> set (inner_verts p)"
  shows "u \<in> set (inner_verts (p @ q))"
  using assms
by (induct p) (auto simp: inner_verts_def)

lemma in_set_inner_verts_appendI_r:
  assumes "u \<in> set (inner_verts q)"
  shows "u \<in> set (inner_verts (p @ q))"
  using assms
by (induct p) (auto simp: inner_verts_def dest: list_set_tl)

end


subsection \<open>Progressing Walks\<close>

text \<open>
  We call a walk \emph{progressing} if it does not contain the sequence
  @{term "[(x,y), (y,x)]"}. This concept is relevant in particular
  for @{term iapath}s: If all of the inner vertices have degree at
  most 2 this implies that such a walk is a trail and even a path.
\<close>

definition progressing :: "('a \<times> 'a) awalk \<Rightarrow> bool" where
  "progressing p \<equiv> \<forall>xs x y ys. p \<noteq> xs @ (x,y) # (y,x) # ys"

lemma progressing_Nil: "progressing []"
  by (auto simp: progressing_def)

lemma progressing_single: "progressing [e]"
  by (auto simp: progressing_def)

lemma progressing_ConsD:
  assumes "progressing (e # es)" shows "progressing es"
  using assms unfolding progressing_def by (metis (no_types) append_eq_Cons_conv)

lemma progressing_Cons:
  "progressing (x # xs) \<longleftrightarrow> (xs = [] \<or> (xs \<noteq> [] \<and> \<not>(fst x = snd (hd xs) \<and> snd x = fst (hd xs)) \<and> progressing xs))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (cases xs)
    case Nil then show ?thesis by auto
  next
    case (Cons x' xs')
    then have "\<And>u v. (x # x' # xs') \<noteq> [] @ (u,v) # (v,u) # xs'" using \<open>?L\<close> unfolding progressing_def by metis
    then have "\<not>(fst x = snd x' \<and> snd x = fst x')" by (cases x) (cases x', auto)
    with Cons show ?thesis using \<open>?L\<close> by (auto dest: progressing_ConsD)
  qed
next
  assume ?R then show ?L unfolding progressing_def
    by (auto simp add: Cons_eq_append_conv)
qed

lemma progressing_Cons_Cons:
  "progressing ((u,v) # (v,w) # es) \<longleftrightarrow> u \<noteq> w \<and> progressing ((v,w) # es)" (is "?L \<longleftrightarrow> ?R")
  by (auto simp: progressing_Cons)

lemma progressing_appendD1:
  assumes "progressing (p @ q)" shows "progressing p"
  using assms unfolding progressing_def by (metis append_Cons append_assoc)

lemma progressing_appendD2:
  assumes "progressing (p @ q)" shows "progressing q"
  using assms unfolding progressing_def by (metis append_assoc)

lemma progressing_rev_path:
  "progressing (rev_path p) = progressing p" (is "?L = ?R")
proof
  assume ?L
  show ?R unfolding progressing_def
  proof (intro allI notI)
    fix xs x y ys l1 l2 assume "p = xs @ (x,y) # (y,x) # ys"
    then have "rev_path p = rev_path ys @ (x,y) # (y,x) # rev_path xs"
      by simp
    then show False using \<open>?L\<close> unfolding progressing_def by auto
  qed
next
  assume ?R
  show ?L unfolding progressing_def
  proof (intro allI notI)
    fix xs x y ys l1 l2 assume "rev_path p = xs @ (x,y) # (y,x) # ys"
    then have "rev_path (rev_path p) = rev_path ys @ (x,y) # (y,x) # rev_path xs"
      by simp
    then show False using \<open>?R\<close> unfolding progressing_def by auto
  qed
qed

lemma progressing_append_iff:
  shows "progressing (xs @ ys) \<longleftrightarrow> progressing xs \<and> progressing ys
      \<and> (xs \<noteq> [] \<and> ys \<noteq> [] \<longrightarrow> (fst (last xs) \<noteq> snd (hd ys) \<or> snd (last xs) \<noteq> fst (hd ys)))"
proof (induct ys arbitrary: xs)
  case Nil then show ?case by (auto simp: progressing_Nil)
next
  case (Cons y' ys')
  let "_ = ?R" = ?case
  have *: "xs \<noteq> [] \<Longrightarrow> hd (rev_path xs) = prod.swap (last xs)" by (induct xs) auto

  have "progressing (xs @ y' # ys') \<longleftrightarrow> progressing ((xs @ [y']) @ ys')"
    by simp
  also have "\<dots> \<longleftrightarrow> progressing (xs @ [y']) \<and> progressing ys' \<and> (ys' \<noteq> [] \<longrightarrow> (fst y' \<noteq> snd (hd ys') \<or> snd y' \<noteq> fst (hd ys')))"
    by (subst Cons) simp
  also have "\<dots> \<longleftrightarrow> ?R"
    by (auto simp: progressing_Cons progressing_Nil progressing_rev_path[where p="xs @ _",symmetric] * progressing_rev_path prod.swap_def)
  finally show ?case .
qed



subsection \<open>Walks with Restricted Vertices\<close>

definition verts3 :: "('a, 'b) pre_digraph \<Rightarrow> 'a set" where
  "verts3 G \<equiv> {v \<in> verts G. 2 < in_degree G v}"

text \<open>A path were only the end nodes may be in @{term V}\<close>

definition (in pre_digraph) gen_iapath :: "'a set \<Rightarrow> 'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "gen_iapath V u p v \<equiv> u \<in> V \<and> v \<in> V \<and> apath u p v \<and> set (inner_verts p) \<inter> V = {} \<and> p \<noteq> []"

abbreviation (in pre_digraph) (input) iapath :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "iapath u p v \<equiv> gen_iapath (verts3 G) u p v"

definition gen_contr_graph :: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a pair_pre_digraph" where
  "gen_contr_graph G V \<equiv> \<lparr>
     pverts = V,
     parcs = {(u,v). \<exists>p. pre_digraph.gen_iapath G V u p v}
     \<rparr>"

abbreviation (input) contr_graph :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "contr_graph G \<equiv> gen_contr_graph G (verts3 G)"



subsection \<open>Properties of subdivisions\<close>

lemma (in pair_sym_digraph) verts3_subdivide:
  assumes "e \<in> parcs G" "w \<notin> pverts G"
  shows"verts3 (subdivide G e w) = verts3 G"
proof -
  let ?sG = "subdivide G e w" 
  obtain u v where e_conv[simp]: "e = (u,v)" by (cases e) auto

  from \<open>w \<notin> pverts G\<close>
  have w_arcs: "(u,w) \<notin> parcs G" "(v,w) \<notin> parcs G" "(w,u) \<notin> parcs G" "(w,v) \<notin> parcs G"
    by (auto dest: wellformed)
  have G_arcs: "(u,v) \<in> parcs G" "(v,u) \<in> parcs G"
    using \<open>e \<in> parcs G\<close> by (auto simp: arcs_symmetric) 

  have "{v \<in> pverts G. 2 < in_degree G v} = {v \<in> pverts G. 2 < in_degree ?sG v}"
  proof -
    { fix x assume "x \<in> pverts G"
      define card_eq where "card_eq x \<longleftrightarrow> in_degree ?sG x = in_degree G x" for x

      have "in_arcs ?sG u = (in_arcs G u - {(v,u)}) \<union> {(w,u)}"
           "in_arcs ?sG v = (in_arcs G v - {(u,v)}) \<union> {(w,v)}"
        using w_arcs G_arcs by auto
      then have "card_eq u" "card_eq v"
        unfolding card_eq_def in_degree_def using w_arcs G_arcs
        apply -
        apply (cases "finite (in_arcs G u)"; simp add: card_Suc_Diff1 del: card_Diff_insert)
        apply (cases "finite (in_arcs G v)"; simp add: card_Suc_Diff1 del: card_Diff_insert)
        done
      moreover
      have "x \<notin> {u,v} \<Longrightarrow> in_arcs ?sG x = in_arcs G x"
        using \<open>x \<in> pverts G\<close> \<open>w \<notin> pverts G\<close> by (auto simp: )
      then have "x \<notin> {u,v} \<Longrightarrow> card_eq x" by (simp add: in_degree_def card_eq_def)
      ultimately have "card_eq x" by fast
      then have "in_degree G x = in_degree ?sG x"
        unfolding card_eq_def by simp }
    then show ?thesis by auto
  qed
  also have "\<dots> = {v\<in>pverts ?sG. 2 < in_degree ?sG v}"
  proof -
    have "in_degree ?sG w \<le> 2"
    proof -
      have "in_arcs ?sG w = {(u,w), (v,w)}"
        using \<open>w \<notin> pverts G\<close> G_arcs(1) by (auto simp: wellformed')
      then show ?thesis
        unfolding in_degree_def by (auto simp: card_insert_if)
    qed
    then show ?thesis using G_arcs assms by auto
  qed
  finally show ?thesis by (simp add: verts3_def)
qed

lemma sd_path_Nil_iff:
  "sd_path e w p = [] \<longleftrightarrow> p = []"
  by (cases "(e,w,p)" rule: sd_path.cases) auto

lemma (in pair_sym_digraph) gen_iapath_sd_path:
  fixes e :: "'a \<times> 'a" and w :: 'a
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  assumes path: "gen_iapath V u p v"
  shows "pre_digraph.gen_iapath (subdivide G e w) V u (sd_path e w p) v"
proof -
  obtain x y where e_conv: "e = (x,y)" by (cases e) auto
  interpret S: pair_sym_digraph "subdivide G e w"
    using elems by (auto intro: pair_sym_digraph_subdivide)

  from path have "apath u p v" by (auto simp: gen_iapath_def)
  then have apath_sd: "S.apath u (sd_path e w p) v" and
    set_ev_sd: "set (S.awalk_verts u (sd_path e w p)) \<subseteq> set (awalk_verts u p) \<union> {w}"
    using elems by (rule apath_sd_path set_awalk_verts_sd_path)+
  have "w \<notin> {u,v}" using elems \<open>apath u p v\<close>
    by (auto simp: apath_def awalk_hd_in_verts awalk_last_in_verts)

  have "set (S.inner_verts (sd_path e w p)) = set (S.awalk_verts u (sd_path e w p)) - {u,v}"
    using apath_sd by (rule S.set_inner_verts)
  also have "\<dots> \<subseteq> set (awalk_verts u p) \<union> {w} - {u,v}"
    using set_ev_sd by auto
  also have "\<dots> = set (inner_verts p) \<union> {w}"
    using set_inner_verts[OF \<open>apath u p v\<close>] \<open>w \<notin> {u,v}\<close> by blast
  finally have "set (S.inner_verts (sd_path e w p)) \<inter> V \<subseteq> (set (inner_verts p) \<union> {w}) \<inter> V"
    using V by blast
  also have "\<dots> \<subseteq> {}"
    using path elems V unfolding gen_iapath_def by auto
  finally show ?thesis
    using apath_sd elems path by (auto simp: gen_iapath_def S.gen_iapath_def sd_path_Nil_iff)
qed

lemma (in pair_sym_digraph)
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  assumes path: "pre_digraph.gen_iapath (subdivide G e w) V u p v"
  shows gen_iapath_co_path: "gen_iapath V u (co_path e w p) v" (is ?thesis_path)
    and set_awalk_verts_co_path': "set (awalk_verts u (co_path e w p)) = set (awalk_verts u p) - {w}" (is ?thesis_set)
proof -
  interpret S: pair_sym_digraph "subdivide G e w"
    using elems by (rule pair_sym_digraph_subdivide)

  have uv: "u \<in> pverts G" "v \<in> pverts G" "S.apath u p v" using V path by (auto simp: S.gen_iapath_def)
  note co = apath_co_path[OF elems uv] set_awalk_verts_co_path[OF elems uv]

  show ?thesis_set by (fact co)
  show ?thesis_path using co path unfolding gen_iapath_def S.gen_iapath_def using elems
    by (clarsimp simp add: set_inner_verts[of u] S.set_inner_verts[of u]) blast
qed



subsection \<open>Pair Graphs\<close>

context pair_sym_digraph begin

lemma gen_iapath_rev_path:
  "gen_iapath V v (rev_path p) u = gen_iapath V u p v" (is "?L = ?R")
proof -
  { fix u p v assume "gen_iapath V u p v"
    then have "butlast (tl (awalk_verts v (rev_path p))) = rev (butlast (tl (awalk_verts u p)))"
      by (auto simp: tl_rev butlast_rev butlast_tl awalk_verts_rev_path gen_iapath_def apath_def)
    with \<open>gen_iapath V u p v\<close> have "gen_iapath V v (rev_path p) u"
      by (auto simp: gen_iapath_def apath_def inner_verts_conv[symmetric] awalk_verts_rev_path) }
  note RL = this
  show ?thesis by (auto dest: RL intro: RL)
qed

lemma inner_verts_rev_path:
  assumes "awalk u p v"
  shows "inner_verts (rev_path p) = rev (inner_verts p)"
by (metis assms butlast_rev butlast_tl awalk_verts_rev_path inner_verts_conv tl_rev)

end

context pair_pseudo_graph begin

lemma apath_imp_progressing:
  assumes "apath u p v" shows "progressing p"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain xs x y ys where *: "p = xs @ (x,y) # (y,x) # ys"
    unfolding progressing_def by auto
  then  have "\<not>apath u p v"
    by (simp add: apath_append_iff apath_simps hd_in_awalk_verts)
  then show False using assms by auto
qed

lemma awalk_Cons_deg2_unique:
  assumes "awalk u p v" "p \<noteq> []"
  assumes "in_degree G u \<le> 2"
  assumes "awalk u1 (e1 # p) v" "awalk u2 (e2 # p) v"
  assumes "progressing (e1 # p)" "progressing (e2 # p)"
  shows "e1 = e2"
proof (cases p)
  case (Cons e es)
  show ?thesis
  proof (rule ccontr)
    assume "e1 \<noteq> e2"
    define x where "x = snd e"
    then have e_unf:"e = (u,x)" using \<open>awalk u p v\<close> Cons by (auto simp: awalk_simps)
    then have ei_unf: "e1 = (u1, u)" "e2 = (u2, u)"
      using Cons assms by (auto simp: apath_simps prod_eqI)
    with Cons assms \<open>e = (u,x)\<close> \<open>e1 \<noteq> e2\<close> have "u1 \<noteq> u2" "x \<noteq> u1" "x \<noteq> u2"
      by (auto simp: progressing_Cons_Cons)
    moreover have "{(u1, u), (u2, u), (x,u)} \<subseteq> parcs G"
      using e_unf ei_unf Cons assms by (auto simp: awalk_simps intro: arcs_symmetric)
    then have "finite (in_arcs G u)"
      and "{(u1, u), (u2, u), (x,u)} \<subseteq> in_arcs G u" by auto
    then have "card ({(u1, u), (u2, u), (x,u)}) \<le> in_degree G u"
      unfolding in_degree_def by (rule card_mono) 
    ultimately show "False" using \<open>in_degree G u \<le> 2\<close> by auto
  qed
qed (simp add: \<open>p \<noteq> []\<close>)

lemma same_awalk_by_same_end:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
    and walk: "awalk u p v" "awalk u q w" "hd p = hd q" "p \<noteq> []" "q \<noteq> []"
    and progress: "progressing p" "progressing q"
    and tail: "v \<in> V" "w \<in> V"
    and inner_verts: "set (inner_verts p) \<inter> V = {}"
      "set (inner_verts q) \<inter> V = {}"
  shows "p = q"
  using walk progress inner_verts
proof (induct p q arbitrary: u rule: list_induct2'[case_names Nil_Nil Cons_Nil Nil_Cons Cons_Cons])
  case (Cons_Cons a as b bs)
  from \<open>hd (a # _) = hd _\<close> have "a = b" by simp

  { fix a as v b bs w
    assume A: "awalk u (a # as) v" "awalk u (b # bs) w"
        "set (inner_verts (b # bs)) \<inter> V = {}" "v \<in> V" "a = b" "as = []"
    then have "bs = []" by - (rule ccontr, auto simp: inner_verts_Cons awalk_simps)
  } note Nil_imp_Nil = this

  show ?case
  proof (cases "as = []")
    case True
    then have "bs = []" using Cons_Cons.prems \<open>a = b\<close> tail by (metis Nil_imp_Nil)
    then show ?thesis using True \<open>a = b\<close> by simp
  next
    case False
    then have "bs \<noteq> []" using Cons_Cons.prems \<open>a = b\<close> tail by (metis Nil_imp_Nil)

    obtain a' as' where "as = a' # as'" using \<open>as \<noteq> []\<close> by (cases as) simp
    obtain b' bs' where "bs = b' # bs'" using \<open>bs \<noteq> []\<close> by (cases bs) simp

    let ?arcs = "{(fst a, snd a), (snd a', snd a), (snd b', snd a)}"

    have "card {fst a, snd a', snd b'} = card (fst ` ?arcs)" by auto
    also have "\<dots> = card ?arcs" by (rule card_image) (cases a, auto)
    also have "\<dots> \<le> in_degree G (snd a)"
    proof -
      have "?arcs \<subseteq> in_arcs G (snd a)"
        using \<open>progressing (a # as)\<close> \<open>progressing (b # bs)\<close> \<open>awalk _ (a # as) _\<close> \<open>awalk _ (b # bs) _\<close>
        unfolding \<open>a = b\<close> \<open>as = _\<close> \<open>bs = _\<close>
        by (cases b; cases a') (auto simp: progressing_Cons_Cons awalk_simps intro: arcs_symmetric) 
      with _show ?thesis unfolding in_degree_def by (rule card_mono) auto
    qed
    also have "\<dots> \<le> 2"
    proof -
      have "snd a \<notin> V" "snd a \<in> pverts G"
        using Cons_Cons.prems \<open>as \<noteq> []\<close> by (auto simp: inner_verts_Cons)
      then show ?thesis using V by (auto simp: verts3_def)
    qed
    finally have "fst a = snd a' \<or> fst a = snd b' \<or> snd a' = snd b'"
      by (auto simp: card_insert_if split: if_splits)
    then have "hd as = hd bs"
      using \<open>progressing (a # as)\<close> \<open>progressing (b # bs)\<close> \<open>awalk _ (a # as) _\<close> \<open>awalk _ (b # bs) _\<close>
      unfolding \<open>a = b\<close> \<open>as = _\<close> \<open>bs = _\<close>
      by (cases b, cases a', cases b') (auto simp: progressing_Cons_Cons awalk_simps)
    then show ?thesis
      using \<open>as \<noteq> []\<close> \<open>bs \<noteq> []\<close> Cons_Cons.prems
      by (auto dest: progressing_ConsD simp: awalk_simps inner_verts_Cons intro!: Cons_Cons)
  qed
qed simp_all

lemma same_awalk_by_common_arc:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  assumes walk: "awalk u p v" "awalk w q x"
  assumes progress: "progressing p" "progressing q"
  assumes iv_not_in_V: "set (inner_verts p) \<inter> V = {}" "set (inner_verts q) \<inter> V = {}"
  assumes ends_in_V: "{u,v,w,x} \<subseteq> V"
  assumes arcs: "e \<in> set p" "e \<in> set q"
  shows "p = q"
proof -
  from arcs obtain p1 p2 where p_decomp: "p = p1 @ e # p2" by (metis in_set_conv_decomp_first)
  from arcs obtain q1 q2 where q_decomp: "q = q1 @ e # q2" by (metis in_set_conv_decomp_first)

  { define p1' q1' where "p1' = rev_path (p1 @ [e])" and "q1' = rev_path (q1 @ [e])"
    then have decomp: "p = rev_path p1' @ p2" "q = rev_path q1' @ q2"
      and "awlast u (rev_path p1') = snd e" "awlast w (rev_path q1') = snd e"
      using p_decomp q_decomp walk by (auto simp: awlast_append awalk_verts_rev_path)
    then have walk': "awalk (snd e) p1' u" "awalk (snd e) q1' w"
      using walk by auto
    moreover have "hd p1' = hd q1'" "p1' \<noteq> []" "q1' \<noteq> []" by (auto simp: p1'_def q1'_def)
    moreover have "progressing p1'" "progressing q1'"
      using progress unfolding decomp by (auto dest: progressing_appendD1 simp: progressing_rev_path)
    moreover
    have "set (inner_verts (rev_path p1')) \<inter> V = {}" "set (inner_verts (rev_path q1')) \<inter> V = {}"
      using iv_not_in_V unfolding decomp
      by (auto intro: in_set_inner_verts_appendI_l in_set_inner_verts_appendI_r)
    then have "u \<in> V" "w \<in> V" "set (inner_verts p1') \<inter> V = {}" "set (inner_verts q1') \<inter> V = {}"
      using ends_in_V iv_not_in_V walk unfolding decomp
      by (auto simp: inner_verts_rev_path)
    ultimately have "p1' = q1'" by (rule same_awalk_by_same_end[OF V]) }
  moreover
  { define p2' q2' where "p2' = e # p2" and "q2' = e # q2"
    then have decomp: "p = p1 @ p2'" "q = q1 @ q2'"
      using p_decomp q_decomp by (auto simp: awlast_append)
    moreover
    have "awlast u p1 = fst e" "awlast w q1 = fst e"
      using p_decomp q_decomp walk by auto
    ultimately
    have *: "awalk (fst e) p2' v" "awalk (fst e) q2' x"
      using walk by auto
    moreover have "hd p2' = hd q2'" "p2' \<noteq> []" "q2' \<noteq> []" by (auto simp: p2'_def q2'_def)
    moreover have "progressing p2'" "progressing q2'"
      using progress unfolding decomp by (auto dest: progressing_appendD2)
    moreover
    have "v \<in> V" "x \<in> V" "set (inner_verts p2') \<inter> V = {}" "set (inner_verts q2') \<inter> V = {}"
      using ends_in_V iv_not_in_V unfolding decomp
      by (auto intro: in_set_inner_verts_appendI_l in_set_inner_verts_appendI_r)
    ultimately have "p2' = q2'" by (rule same_awalk_by_same_end[OF V]) }
  ultimately
  show "p = q" using p_decomp q_decomp by (auto simp: rev_path_eq)
qed

lemma same_gen_iapath_by_common_arc:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  assumes path: "gen_iapath V u p v" "gen_iapath V w q x"
  assumes arcs: "e \<in> set p" "e \<in> set q"
  shows "p = q"
proof -
  from path have awalk: "awalk u p v" "awalk w q x" "progressing p" "progressing q"
      and in_V: "set (inner_verts p) \<inter> V = {}" "set (inner_verts q) \<inter> V = {}" "{u,v,w,x} \<subseteq> V"
    by (auto simp: gen_iapath_def apath_imp_progressing apath_def)
  from V awalk in_V arcs show ?thesis by (rule same_awalk_by_common_arc)
qed


end



subsection \<open>Slim graphs\<close>

text \<open>
  We define the notion of a slim graph. The idea is that for a slim graph @{term G}, @{term G}
  is a subdivision of @{term "contr_graph G"}.
\<close>

context pair_pre_digraph begin

definition (in pair_pre_digraph) is_slim :: "'a set \<Rightarrow> bool" where
  "is_slim V \<equiv>
    (\<forall>v \<in> pverts G. v \<in> V \<or>
      in_degree G v \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> v \<in> set (awalk_verts x p))) \<and>
    (\<forall>e \<in> parcs G. fst e \<noteq> snd e \<and> (\<exists>x p y. gen_iapath V x p y \<and> e \<in> set p)) \<and>
    (\<forall>u v p q. (gen_iapath V u p v \<and> gen_iapath V u q v) \<longrightarrow> p = q) \<and>
    V \<subseteq> pverts G"

definition direct_arc :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  "direct_arc uv \<equiv> SOME e. {fst uv , snd uv} = {fst e, snd e}"

definition choose_iapath :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) awalk" where
  "choose_iapath u v \<equiv> (let
      chosen_path = (\<lambda>u v. SOME p. iapath u p v)
    in if direct_arc (u,v) = (u,v) then chosen_path u v else rev_path (chosen_path v u))"

(* XXX: Replace "parcs (contr_graph G)" by its definition *)
definition slim_paths :: "('a \<times> ('a \<times> 'a) awalk \<times> 'a) set" where
  "slim_paths \<equiv> (\<lambda>e. (fst e, choose_iapath (fst e) (snd e), snd e)) ` parcs (contr_graph G)"

definition slim_verts :: "'a set" where
  "slim_verts \<equiv> verts3 G \<union> (\<Union>(u,p,_) \<in> slim_paths. set (awalk_verts u p))"

definition slim_arcs :: "'a rel" where
  "slim_arcs \<equiv> \<Union>(_,p,_) \<in> slim_paths. set p"

text \<open>Computes a slim subgraph for an arbitrary @{term pair_digraph}\<close>
definition slim :: "'a pair_pre_digraph" where
  "slim \<equiv> \<lparr> pverts = slim_verts, parcs = slim_arcs \<rparr>" 

end

lemma (in wf_digraph) iapath_dist_ends: "\<And>u p v. iapath u p v \<Longrightarrow> u \<noteq> v"
  unfolding pre_digraph.gen_iapath_def by (metis apath_ends)


context pair_sym_digraph begin

lemma choose_iapath:
  assumes "\<exists>p. iapath u p v"
  shows "iapath u (choose_iapath u v) v"
proof (cases "direct_arc (u,v) = (u,v)")
  define chosen where "chosen u v = (SOME p. iapath u p v)" for u v
  { case True
    have "iapath u (chosen u v) v"
      unfolding chosen_def by (rule someI_ex) (rule assms)
    then show ?thesis using True by (simp add: choose_iapath_def chosen_def) }

  { case False
    from assms obtain p where "iapath u p v" by auto
    then have "iapath v (rev_path p) u"
      by (simp add: gen_iapath_rev_path)
    then have "iapath v (chosen v u) u"
      unfolding chosen_def by (rule someI)
    then show ?thesis using False
      by (simp add: choose_iapath_def chosen_def gen_iapath_rev_path) }
qed

lemma slim_simps: "pverts slim = slim_verts" "parcs slim = slim_arcs"
  by (auto simp: slim_def)

lemma slim_paths_in_G_E:
  assumes "(u,p,v) \<in> slim_paths" obtains "iapath u p v" "u \<noteq> v"
  using assms choose_iapath
  by (fastforce simp: gen_contr_graph_def slim_paths_def dest: iapath_dist_ends)

lemma verts_slim_in_G: "pverts slim \<subseteq> pverts G"
  by (auto simp: slim_simps slim_verts_def verts3_def gen_iapath_def apath_def
    elim!: slim_paths_in_G_E elim!: awalkE)

lemma verts3_in_slim_G[simp]:
  assumes "x \<in> verts3 G" shows "x \<in> pverts slim"
using assms by (auto simp: slim_simps slim_verts_def)

lemma arcs_slim_in_G: "parcs slim \<subseteq> parcs G"
  by (auto simp: slim_simps slim_arcs_def gen_iapath_def apath_def
      elim!: slim_paths_in_G_E elim!: awalkE)

lemma slim_paths_in_slimG:
  assumes "(u,p,v) \<in> slim_paths"
  shows "pre_digraph.gen_iapath slim (verts3 G) u p v \<and> p \<noteq> []"
proof -
  from assms have arcs: "\<And>e. e \<in> set p \<Longrightarrow> e \<in> parcs slim"
    by (auto simp: slim_simps slim_arcs_def)
  moreover
  from assms have "gen_iapath (verts3 G) u p v" and "p \<noteq> []"
    by (auto simp: gen_iapath_def elim!: slim_paths_in_G_E)
  ultimately show ?thesis
    by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
      inner_verts_with_proj_def)
qed

lemma direct_arc_swapped:
  "direct_arc (u,v) = direct_arc (v,u)"
by (simp add: direct_arc_def insert_commute)

lemma direct_arc_chooses:
  fixes u v :: 'a shows "direct_arc (u,v) = (u,v) \<or> direct_arc (u,v) = (v,u)"
proof -
  define f :: "'a set \<Rightarrow> 'a \<times> 'a"
    where "f X = (SOME e. X = {fst e,snd e})" for X

  have "\<exists>p::'a \<times> 'a. {u,v} = {fst p, snd p}" by (rule exI[where x="(u,v)"]) auto
  then have "{u,v} = {fst (f {u,v}), snd (f {u,v})}"
    unfolding f_def by (rule someI_ex)
  then have "f {u,v} = (u,v) \<or> f {u,v} = (v,u)"
    by (auto simp: doubleton_eq_iff prod_eq_iff)
  then show ?thesis by (auto simp: direct_arc_def f_def)
qed

lemma rev_path_choose_iapath:
  assumes "u \<noteq> v"
  shows "rev_path (choose_iapath u v) = choose_iapath v u"
  using assms direct_arc_chooses[of u v]
  by (auto simp: choose_iapath_def direct_arc_swapped)

lemma no_loops_in_iapath: "gen_iapath V u p v \<Longrightarrow> a \<in> set p \<Longrightarrow> fst a \<noteq> snd a"
  by (auto simp: gen_iapath_def no_loops_in_apath)

lemma pair_bidirected_digraph_slim: "pair_bidirected_digraph slim"
proof
  fix e assume A: "e \<in> parcs slim"
  then obtain u p v where "(u,p,v) \<in> slim_paths" "e \<in> set p" by (auto simp: slim_simps slim_arcs_def)
  with A have "iapath u p v" by (auto elim: slim_paths_in_G_E)
  with \<open>e \<in> set p\<close> have "fst e \<in> set (awalk_verts u p)" "snd e \<in> set (awalk_verts u p)"
    by (auto simp: set_awalk_verts gen_iapath_def apath_def)
  moreover  
  from \<open>_ \<in> slim_paths\<close> have "set (awalk_verts u p) \<subseteq> pverts slim"
    by (auto simp: slim_simps slim_verts_def)
  ultimately
  show "fst e \<in> pverts slim" "snd e \<in> pverts slim" by auto

  show "fst e \<noteq> snd e"
    using \<open>iapath u p v\<close> \<open>e \<in> set p \<close> by (auto dest: no_loops_in_iapath)
next
  { fix e assume "e \<in> parcs slim"
    then obtain u p v where "(u,p,v) \<in> slim_paths" and "e \<in> set p"
      by (auto simp: slim_simps slim_arcs_def)
    moreover
    then have "iapath u p v" and "p \<noteq> []" and "u \<noteq> v" by (auto elim: slim_paths_in_G_E)
    then have "iapath v (rev_path p) u" and "rev_path p \<noteq> []" and "v \<noteq> u"
      by (auto simp: gen_iapath_rev_path)
    then have "(v,u) \<in> parcs (contr_graph G)"
      by (auto simp: gen_contr_graph_def)
    moreover
    from \<open>iapath u p v\<close> have "u \<noteq> v"
      by (auto simp: gen_iapath_def dest: apath_nonempty_ends)
    ultimately
    have "(v, rev_path p, u) \<in> slim_paths"
      by (auto simp: slim_paths_def rev_path_choose_iapath intro: rev_image_eqI)
    moreover
    from \<open>e \<in> set p\<close> have "(snd e, fst e) \<in> set (rev_path p)"
      by (induct p) auto
    ultimately have "(snd e, fst e) \<in> parcs slim"
     by (auto simp: slim_simps slim_arcs_def) }
  then show "symmetric slim"
    unfolding symmetric_conv by simp (metis fst_conv snd_conv)
qed


lemma (in pair_pseudo_graph) pair_graph_slim: "pair_graph slim"
proof -
  interpret slim: pair_bidirected_digraph slim by (rule pair_bidirected_digraph_slim)
  show ?thesis
  proof
    show "finite (pverts slim)"
      using verts_slim_in_G finite_verts by (rule finite_subset)
    show "finite (parcs slim)"
      using arcs_slim_in_G finite_arcs by (rule finite_subset)
  qed
qed

lemma subgraph_slim: "subgraph slim G"
proof (rule subgraphI)
  interpret H: pair_bidirected_digraph "slim"
    by (rule pair_bidirected_digraph_slim) intro_locales

  show "verts slim \<subseteq> verts G" "arcs slim \<subseteq> arcs G"
    by (auto simp: verts_slim_in_G arcs_slim_in_G)
  show "compatible G slim" ..
  show "wf_digraph slim" "wf_digraph G"
    by unfold_locales
qed

lemma giapath_if_slim_giapath:
  assumes "pre_digraph.gen_iapath slim (verts3 G) u p v"
  shows "gen_iapath (verts3 G) u p v"
using assms verts_slim_in_G arcs_slim_in_G
by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
  inner_verts_with_proj_def)

lemma slim_giapath_if_giapath:
assumes "gen_iapath (verts3 G) u p v"
  shows "\<exists>p. pre_digraph.gen_iapath slim (verts3 G) u p v" (is "\<exists>p. ?P p")
proof
  from assms have choose_arcs: "\<And>e. e \<in> set (choose_iapath u v) \<Longrightarrow> e \<in> parcs slim"
    by (fastforce simp: slim_simps slim_arcs_def slim_paths_def gen_contr_graph_def)
  moreover
  from assms have choose: "iapath u (choose_iapath u v) v"
    by (intro choose_iapath) (auto simp: gen_iapath_def)
  ultimately show "?P (choose_iapath u v)"
    by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
      inner_verts_with_proj_def)
qed

lemma contr_graph_slim_eq:
   "gen_contr_graph slim (verts3 G) = contr_graph G"
  using giapath_if_slim_giapath slim_giapath_if_giapath by (fastforce simp: gen_contr_graph_def)

end

context pair_pseudo_graph begin

lemma verts3_slim_in_verts3:
  assumes "v \<in> verts3 slim" shows "v \<in> verts3 G"
proof -
  from assms have "2 < in_degree slim v" by (auto simp: verts3_def)
  also have "\<dots> \<le> in_degree G v" using subgraph_slim by (rule subgraph_in_degree)
  finally show ?thesis using assms subgraph_slim by (fastforce simp: verts3_def)
qed

lemma slim_is_slim:
  "pair_pre_digraph.is_slim slim (verts3 G)"
proof (unfold pair_pre_digraph.is_slim_def, safe)
  interpret S: pair_graph slim by (rule pair_graph_slim)
  { fix v assume "v \<in> pverts slim" "v \<notin> verts3 G"
    then have "in_degree G v \<le> 2"
      using verts_slim_in_G by (auto simp: verts3_def)
    then show "in_degree slim v \<le> 2"
      using subgraph_in_degree[OF subgraph_slim, of v] by fastforce
  next
    fix w assume "w \<in> pverts slim" "w \<notin> verts3 G"
    then obtain u p v where upv: "(u, p, v) \<in> slim_paths" "w \<in> set (awalk_verts u p)"
      by (auto simp: slim_simps slim_verts_def)
    moreover
    then have "S.gen_iapath (verts3 G) u p v"
      using slim_paths_in_slimG by auto
    ultimately
    show "\<exists>x q y. S.gen_iapath (verts3 G) x q y
      \<and> w \<in> set (awalk_verts x q)"
      by auto
  next
    fix u v assume "(u,v) \<in> parcs slim"
    then obtain x p y where "(x, p, y) \<in> slim_paths" "(u,v) \<in> set p"
      by (auto simp: slim_simps slim_arcs_def)
    then have "S.gen_iapath (verts3 G) x p y \<and> (u,v) \<in> set p"
      using slim_paths_in_slimG by auto
    then show "\<exists>x p y. S.gen_iapath (verts3 G) x p y \<and> (u,v) \<in> set p"
      by blast
  next
    fix u v assume "(u,v) \<in> parcs slim" "fst (u,v) = snd (u,v)"
    then show False by (auto simp: S.no_loops')
  next
    fix u v p q
    assume paths: "S.gen_iapath (verts3 G) u p v"
          "S.gen_iapath (verts3 G) u q v"

    have V: "verts3 slim \<subseteq> verts3 G" "verts3 G \<subseteq> pverts slim"
      by (auto simp: verts3_slim_in_verts3)
  
    have "p = [] \<or> q = [] \<Longrightarrow> p = q" using paths
      by (auto simp: S.gen_iapath_def dest: S.apath_ends)
    moreover
    { assume "p \<noteq> []" "q \<noteq> []"
      { fix u p v assume "p \<noteq> []" and path: "S.gen_iapath (verts3 G) u p v"
        then obtain e where "e \<in> set p" by (metis last_in_set)
        then have "e \<in> parcs slim" using path by (auto simp: S.gen_iapath_def S.apath_def)
        then obtain x r y where "(x,r,y) \<in> slim_paths" "e \<in> set r"
          by (auto simp: slim_simps slim_arcs_def)
        then have "S.gen_iapath (verts3 G) x r y" by (metis slim_paths_in_slimG)
        with \<open>e \<in> set r\<close> \<open>e \<in> set p\<close> path have "p = r"
          by (auto intro: S.same_gen_iapath_by_common_arc[OF V])
        then have "x = u" "y = v" using path \<open>S.gen_iapath (verts3 G) x r y\<close> \<open>p = r\<close> \<open>p \<noteq> []\<close>
          by (auto simp: S.gen_iapath_def S.apath_def dest: S.awalk_ends)
        then have "(u,p,v) \<in> slim_paths" using \<open>p = r\<close> \<open>(x,r,y) \<in> slim_paths\<close> by simp }
      note obt = this
      from \<open>p \<noteq> []\<close> \<open>q \<noteq> []\<close> paths have "(u,p,v) \<in> slim_paths" "(u,q,v) \<in> slim_paths"
        by (auto intro: obt)
      then have "p = q" by (auto simp: slim_paths_def)
    }
    ultimately show "p = q" by metis
  }
qed auto

end

context pair_sym_digraph begin

lemma
  assumes p: "gen_iapath (pverts G) u p v"
  shows gen_iapath_triv_path: "p = [(u,v)]"
    and gen_iapath_triv_arc: "(u,v) \<in> parcs G"
proof -
  have "set (inner_verts p) = {}"
  proof -
    have *: "\<And>A B :: 'a set. \<lbrakk>A \<subseteq> B; A \<inter> B = {}\<rbrakk> \<Longrightarrow> A = {}" by blast
    have "set (inner_verts p) = set (awalk_verts u p) - {u, v}"
      using p by (simp add: set_inner_verts gen_iapath_def)
    also have "\<dots> \<subseteq> pverts G"
      using p unfolding gen_iapath_def apath_def awalk_conv by auto
    finally show ?thesis
      using p by (rule_tac *) (auto simp: gen_iapath_def)
  qed
  then have "inner_verts p = []" by simp
  then show "p = [(u,v)]" using p
    by (cases p) (auto simp: gen_iapath_def apath_def inner_verts_def split: if_split_asm)
  then show "(u,v) \<in> parcs G"
    using p by (auto simp: gen_iapath_def apath_def)
qed

lemma gen_contr_triv:
  assumes "is_slim V" "pverts G = V" shows "gen_contr_graph G V = G"
proof -
  let ?gcg = "gen_contr_graph G V"

  from assms have "pverts ?gcg = pverts G"
    by (auto simp: gen_contr_graph_def is_slim_def)
  moreover
  have "parcs ?gcg = parcs G"
  proof (rule set_eqI, safe)
    fix u v assume "(u,v) \<in> parcs ?gcg"
    then obtain p where "gen_iapath V u p v"
      by (auto simp: gen_contr_graph_def)
    then show "(u,v) \<in> parcs G"
      using gen_iapath_triv_arc \<open>pverts G = V\<close> by auto
  next
    fix u v assume "(u,v) \<in> parcs G"
    with assms obtain x p y where path: "gen_iapath V x p y" "(u,v) \<in> set p" "u \<noteq> v"
      by (auto simp: is_slim_def)                              
    with \<open>pverts G = V\<close> have "p = [(x,y)]" by (intro gen_iapath_triv_path) auto
    then show "(u,v) \<in> parcs ?gcg"
      using path by (auto simp: gen_contr_graph_def)
  qed
  ultimately
  show "?gcg = G" by auto
qed

lemma is_slim_no_loops:
  assumes "is_slim V" "a \<in> arcs G" shows "fst a \<noteq> snd a"
  using assms by (auto simp: is_slim_def)

end



subsection \<open>Contraction Preserves Kuratowski-Subgraph-Property\<close>

lemma (in pair_pseudo_graph) in_degree_contr:
  assumes "v \<in> V" and V: "verts3 G \<subseteq> V" "V \<subseteq> verts G"
  shows "in_degree (gen_contr_graph G V) v \<le> in_degree G v"
proof -
  have fin: "finite {(u, p). gen_iapath V u p v}"
  proof -
    have "{(u, p). gen_iapath V u p v} \<subseteq> (\<lambda>(u,p,_). (u,p)) ` {(u,p,v). apath u p v}"
      by (force simp: gen_iapath_def)
    with apaths_finite_triple show ?thesis by (rule finite_surj)
  qed

  have io_snd: "inj_on snd {(u,p). gen_iapath V u p v}"
    by (rule inj_onI) (auto simp: gen_iapath_def apath_def dest: awalk_ends)

  have io_last: "inj_on last {p. \<exists>u. gen_iapath V u p v}"
  proof (rule inj_onI, safe)
    fix u1 u2 p1 p2
    assume A: "last p1 = last p2" and B: "gen_iapath V u1 p1 v" "gen_iapath V u2 p2 v"
    from B have "last p1 \<in> set p1" "last p2 \<in> set p2" by (auto simp: gen_iapath_def)
    with A have "last p1 \<in> set p1" "last p1 \<in> set p2" by simp_all
    with V[simplified] B show "p1 = p2" by (rule same_gen_iapath_by_common_arc)
  qed

  have "in_degree (gen_contr_graph G V) v = card ((\<lambda>(u,_). (u,v)) ` {(u,p). gen_iapath V u p v})"
  proof -
    have "in_arcs (gen_contr_graph G V) v = (\<lambda>(u,_). (u,v)) ` {(u,p). gen_iapath V u p v}"
      by (auto simp: gen_contr_graph_def)
    then show ?thesis unfolding in_degree_def by simp
  qed
  also have "\<dots> \<le> card {(u,p). gen_iapath V u p v}"
    using fin by (rule card_image_le)
  also have "\<dots> = card (snd ` {(u,p). gen_iapath V u p v})"
    using io_snd by (rule card_image[symmetric])
  also have "snd ` {(u,p). gen_iapath V u p v} = {p. \<exists>u. gen_iapath V u p v}"
    by (auto intro: rev_image_eqI)
  also have "card \<dots> = card (last ` ...)"
    using io_last by (rule card_image[symmetric])
  also have "\<dots> \<le> in_degree G v"
    unfolding in_degree_def
  proof (rule card_mono)
    show "last ` {p. \<exists>u. gen_iapath V u p v} \<subseteq> in_arcs G v"
    proof -
      have "\<And>u p. awalk u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> last p \<in> parcs G"
        by (auto simp: awalk_def)
      moreover 
      { fix u p assume "awalk u p v" "p \<noteq> []"
        then have "snd (last p) = v" by (induct p arbitrary: u) (auto simp: awalk_simps) }
      ultimately
      show ?thesis unfolding in_arcs_def by (auto simp: gen_iapath_def apath_def)
    qed
  qed auto
  finally show ?thesis .
qed

lemma (in pair_graph) contracted_no_degree2_simp:
  assumes subd: "subdivision_pair G H"
  assumes two_less_deg2: "verts3 G = pverts G"
  shows "contr_graph H = G"
  using subd
proof (induct rule: subdivision_pair_induct)
  case base

  { fix e assume "e \<in> parcs G"
    then have "gen_iapath (pverts G) (fst e) [(fst e, snd e)] (snd e)" "e \<in> set [(fst e, snd e)]"
      using no_loops[of "(fst e, snd e)"] by (auto simp: gen_iapath_def apath_simps )
    then have "\<exists>u p v. gen_iapath (pverts G) u p v \<and> e \<in> set p" by blast }
  moreover
  { fix u p v assume "gen_iapath (pverts G) u p v"
    from \<open>gen_iapath _ u p v\<close> have "p = [(u,v)]"
      unfolding gen_iapath_def apath_def
      by safe (cases p, case_tac [2] list, auto simp: awalk_simps inner_verts_def) }
  ultimately have "is_slim (verts3 G)" unfolding is_slim_def two_less_deg2
    by (blast dest: no_loops_in_iapath)
  then show ?case by (simp add: gen_contr_triv two_less_deg2)
next
  case (divide e w H)
  let ?sH = "subdivide H e w"
  from \<open>subdivision_pair G H\<close> interpret H: pair_bidirected_digraph H
    by (rule bidirected_digraphI_subdivision)
  from divide(1,2) interpret S: pair_sym_digraph ?sH by (rule H.pair_sym_digraph_subdivide)
  obtain u v where e_conv:"e = (u,v)" by (cases e) auto
  have "contr_graph ?sH = contr_graph H"
  proof -
    have V_cond: "verts3 H \<subseteq> pverts H" by (auto simp: verts3_def)
    have "verts3 H = verts3 ?sH"
      using divide by (simp add: H.verts3_subdivide)
    then have v: "pverts (contr_graph ?sH) = pverts (contr_graph H)"
      by (auto simp: gen_contr_graph_def)
    moreover
    then have "parcs (contr_graph ?sH) = parcs (contr_graph H)"
      unfolding gen_contr_graph_def
      by (auto dest: H.gen_iapath_co_path[OF divide(1,2) V_cond]
          H.gen_iapath_sd_path[OF divide(1,2) V_cond])
    ultimately show ?thesis by auto
  qed
  then show ?case using divide by simp
qed

(* could be generalized *)
lemma verts3_K33:
  assumes "K\<^bsub>3,3\<^esub> (with_proj G)"
  shows "verts3 G = verts G"
proof -
  { fix v assume "v \<in> pverts G"
    from assms obtain U V where cards: "card U = 3" "card V=3"
      and UV: "U \<inter> V = {}" "pverts G = U \<union> V" "parcs G = U \<times> V \<union> V \<times> U"
      unfolding complete_bipartite_digraph_pair_def by blast
    have "2 < in_degree G v"
    proof (cases "v \<in> U")
      case True
      then have "in_arcs G v = V \<times> {v}" using UV by fastforce
      then show ?thesis using cards by (auto simp: card_cartesian_product in_degree_def)
    next
      case False
      then have "in_arcs G v = U \<times> {v}" using \<open>v \<in> _\<close> UV by fastforce
      then show ?thesis using cards by (auto simp: card_cartesian_product in_degree_def)
    qed }
  then show ?thesis by (auto simp: verts3_def)
qed

(* could be generalized *)
lemma verts3_K5:
  assumes "K\<^bsub>5\<^esub> (with_proj G)"
  shows "verts3 G = verts G"
proof -
  interpret pgG: pair_graph G using assms by (rule pair_graphI_complete)
  { fix v assume "v \<in> pverts G"
    have "2 < (4 :: nat)" by simp
    also have "4 = card (pverts G - {v})"
      using assms \<open>v \<in> pverts G\<close> unfolding complete_digraph_def by auto
    also have "pverts G - {v} = {u \<in> pverts G. u \<noteq> v}"
      by auto
    also have "card \<dots> = card ({u \<in> pverts G. u \<noteq> v} \<times> {v})" (is "_ = card ?A")
      by auto
    also have "?A = in_arcs G v"
      using assms \<open>v \<in> pverts G\<close> unfolding complete_digraph_def by safe auto
    also have "card \<dots> = in_degree G v"
      unfolding in_degree_def ..
    finally have "2 < in_degree G v" . }
  then show ?thesis unfolding verts3_def by auto
qed

lemma K33_contractedI:
  assumes subd: "subdivision_pair G H"
  assumes k33: "K\<^bsub>3,3\<^esub> G"
  shows "K\<^bsub>3,3\<^esub> (contr_graph H)"
proof -
  interpret pgG: pair_graph G using k33 by (rule pair_graphI_complete_bipartite)
  show ?thesis
    using assms by (auto simp: pgG.contracted_no_degree2_simp verts3_K33)
qed

lemma K5_contractedI:
  assumes subd: "subdivision_pair G H"
  assumes k5: "K\<^bsub>5\<^esub> G"
  shows "K\<^bsub>5\<^esub> (contr_graph H)"
proof -
  interpret pgG: pair_graph G using k5 by (rule pair_graphI_complete)
  show ?thesis
    using assms by (auto simp add: pgG.contracted_no_degree2_simp verts3_K5)
qed



subsection \<open>Final proof\<close>

context pair_sym_digraph begin


lemma gcg_subdivide_eq:
  assumes mem: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  shows "gen_contr_graph (subdivide G e w) V = gen_contr_graph G V"
proof -
  interpret sdG: pair_sym_digraph "subdivide G e w"
    using mem by (rule pair_sym_digraph_subdivide)
  { fix u p v assume "sdG.gen_iapath V u p v"
    have "gen_iapath V u (co_path e w p) v"
      using mem V \<open>sdG.gen_iapath V u p v\<close> by (rule gen_iapath_co_path)
    then have "\<exists>p. gen_iapath V u p v" ..
  } note A = this
  moreover
  { fix u p v assume "gen_iapath V u p v"
    have "sdG.gen_iapath V u (sd_path e w p) v"
      using mem V \<open>gen_iapath V u p v\<close> by (rule gen_iapath_sd_path)
    then have "\<exists>p. sdG.gen_iapath V u p v" ..
  } note B = this
  ultimately show ?thesis using assms by (auto simp: gen_contr_graph_def)
qed

lemma co_path_append:
  assumes "[last p1, hd p2] \<notin> {[(fst e,w),(w,snd e)], [(snd e,w),(w,fst e)]}"
  shows "co_path e w (p1 @ p2) = co_path e w p1 @ co_path e w p2"
using assms
proof (induct p1 rule: co_path_induct)
  case single then show ?case by (cases p2) auto
next
  case (co e1 e2 es) then show ?case by (cases es) auto
next
  case (corev e1 e2 es) then show ?case by (cases es) auto
qed auto

lemma exists_co_path_decomp1:
  assumes mem: "e \<in> parcs G" "w \<notin> pverts G"
  assumes p: "pre_digraph.apath (subdivide G e w) u p v" "(fst e, w) \<in> set p" "w \<noteq> v"
  shows "\<exists>p1 p2. p = p1 @ (fst e, w) # (w, snd e) # p2"
proof -
  let ?sdG = "subdivide G e w"
  interpret sdG: pair_sym_digraph ?sdG
    using mem by (rule pair_sym_digraph_subdivide)
  obtain p1 p2 z where p_decomp: "p = p1 @ (fst e, w) # (w, z) # p2" "fst e \<noteq> z" "w \<noteq> z"
    by atomize_elim (rule sdG.apath_succ_decomp[OF p])
  then have "(fst e,w) \<in> parcs ?sdG" "(w, z) \<in> parcs ?sdG"
    using p by (auto simp: sdG.apath_def)
  with \<open>fst e \<noteq> z\<close> have "z = snd e"
    using mem by (cases e) (auto simp: wellformed')
  with p_decomp show ?thesis by fast
qed

lemma is_slim_if_subdivide:
  assumes "pair_pre_digraph.is_slim (subdivide G e w) V"
  assumes mem1: "e \<in> parcs G" "w \<notin> pverts G" and mem2: "w \<notin> V"
  shows "is_slim V"
proof -
  let ?sdG = "subdivide G e w"
  interpret sdG: pair_sym_digraph "subdivide G e w"
    using mem1 by (rule pair_sym_digraph_subdivide)
  obtain u v where "e = (u,v)" by (cases e) auto
  with mem1 have "u \<in> pverts G" "v \<in> pverts G" by (auto simp: wellformed')
  with mem1  have "u \<noteq> w" "v \<noteq> w" by auto

  let ?w_parcs = "{(u,w), (v,w), (w,u), (w, v)}"
  have sdg_new_parcs: "?w_parcs \<subseteq> parcs ?sdG"
    using \<open>e = (u,v)\<close> by auto
  have sdg_no_parcs: "(u,v) \<notin> parcs ?sdG" "(v,u) \<notin> parcs ?sdG"
    using \<open>e = (u,v)\<close> \<open>u \<noteq> w\<close> \<open>v \<noteq> w\<close> by auto

  { fix z assume A: "z \<in> pverts G"
    have "in_degree ?sdG z = in_degree G z"
    proof -
      { assume "z \<noteq> u" "z \<noteq> v"
        then have "in_arcs ?sdG z = in_arcs G z"
          using \<open>e = (u,v)\<close> mem1 A by auto
        then have "in_degree ?sdG z = in_degree G z" by (simp add: in_degree_def) }
      moreover
      { assume "z = u"
        then have "in_arcs G z = in_arcs ?sdG z \<union> {(v,u)} - {(w,u)}"
          using \<open>e = (u,v)\<close> mem1 by (auto simp: intro: arcs_symmetric wellformed')
        moreover
        have "card (in_arcs ?sdG z \<union> {(v,u)} - {(w,u)}) = card (in_arcs ?sdG z)"
          using sdg_new_parcs sdg_no_parcs \<open>z = u\<close> by (cases "finite (in_arcs ?sdG z)") (auto simp: in_arcs_def)
        ultimately have "in_degree ?sdG z= in_degree G z" by (simp add: in_degree_def) }
      moreover
      { assume "z = v"
        then have "in_arcs G z = in_arcs ?sdG z \<union> {(u,v)} - {(w,v)}"
          using \<open>e = (u,v)\<close> mem1 A by (auto simp: wellformed')
        moreover
        have "card (in_arcs ?sdG z \<union> {(u,v)} - {(w,v)}) = card (in_arcs ?sdG z)"
          using sdg_new_parcs sdg_no_parcs \<open>z = v\<close> by (cases "finite (in_arcs ?sdG z)") (auto simp: in_arcs_def)
        ultimately have "in_degree ?sdG z= in_degree G z" by (simp add: in_degree_def) }
      ultimately show ?thesis by metis
    qed }
  note in_degree_same = this

  have V_G: "V \<subseteq> pverts G" "verts3 G \<subseteq> V"
  proof -
    have "V \<subseteq> pverts ?sdG" "pverts ?sdG = pverts G \<union> {w}" "verts3 ?sdG \<subseteq> V" "verts3 G \<subseteq> verts3 ?sdG"
      using \<open>sdG.is_slim V\<close> \<open>e = (u,v)\<close> in_degree_same mem1
      unfolding sdG.is_slim_def verts3_def
      by (fast, simp, fastforce, force)
    then show "V \<subseteq> pverts G" "verts3 G \<subseteq> V" using \<open>w \<notin> V\<close> by auto
  qed

  have pverts: "\<forall>v\<in>pverts G. v \<in> V \<or> in_degree G v \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> v \<in> set (awalk_verts x p))"
  proof -
    { fix z assume A: "z \<in> pverts G" "z \<notin> V"
      have "z \<in> pverts ?sdG" using \<open>e = (u,v)\<close> A mem1 by auto
      then have "in_degree ?sdG z \<le> 2"
        using \<open>sdG.is_slim V\<close> A by (auto simp: sdG.is_slim_def)
      with in_degree_same[OF \<open>z \<in> pverts G\<close>] have idg: "in_degree G z \<le> 2" by auto

      from A have "z \<in> pverts ?sdG" "z \<notin> V" using \<open>e = (u,v)\<close> mem1 by auto
      then obtain x' q y' where "sdG.gen_iapath V x' q y'" "z \<in> set (sdG.awalk_verts x' q)"
        using \<open>sdG.is_slim V\<close> unfolding sdG.is_slim_def by metis
      then have "gen_iapath V x' (co_path e w q) y'" "z \<in> set (awalk_verts x' (co_path e w q))"
        using A mem1 V_G by (auto simp: set_awalk_verts_co_path' intro: gen_iapath_co_path)
      with idg have "in_degree G z \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> z \<in> set (awalk_verts x p))"
        by metis }
    then show ?thesis by auto
  qed

  have parcs: "\<forall>e\<in>parcs G. fst e \<noteq> snd e \<and> (\<exists>x p y. gen_iapath V x p y \<and> e \<in> set p)"
  proof (intro ballI conjI)
    fix e' assume "e' \<in> parcs G"

    show "(\<exists>x p y. gen_iapath V x p y \<and> e' \<in> set p)"
    proof (cases "e' \<in> parcs ?sdG")
      case True
      then obtain x p y where "sdG.gen_iapath V x p y" "e' \<in> set p"
        using \<open>sdG.is_slim V\<close> by (auto simp: sdG.is_slim_def)
      with \<open>e \<in> parcs G\<close> \<open>w \<notin> pverts G\<close> V_G have "gen_iapath V x (co_path e w p) y"
        by (auto intro: gen_iapath_co_path)

      from \<open>e' \<in> parcs G\<close> have "e' \<notin> ?w_parcs" using mem1 by (auto simp: wellformed')
      with \<open>e' \<in> set p\<close> have "e' \<in> set (co_path e w p)"
        by (induct p rule: co_path_induct) (force simp: \<open>e = (u,v)\<close>)+
      then show "\<exists>x p y. gen_iapath V x p y \<and> e' \<in> set p "
        using \<open>gen_iapath V x (co_path e w p) y\<close>  by fast
    next
      assume "e' \<notin> parcs ?sdG"
      define a b where "a = fst e'" and "b = snd e'"
      then have "e' = (a,b)" and ab: "(a,b) = (u,v) \<or> (a,b) = (v,u)"
        using \<open>e' \<in> parcs G\<close> \<open>e' \<notin> parcs ?sdG\<close> \<open>e = (u,v)\<close> mem1 by auto
      obtain x p y where "sdG.gen_iapath V x p y" "(a,w) \<in> set p"
        using \<open>sdG.is_slim V\<close> sdg_new_parcs ab by (auto simp: sdG.is_slim_def)
      with \<open>e \<in> parcs G\<close> \<open>w \<notin> pverts G\<close> V_G have "gen_iapath V x (co_path e w p) y"
        by (auto intro: gen_iapath_co_path)

      have "(a,b) \<in> parcs G" "subdivide G (a,b) w = subdivide G e w"
        using mem1 \<open>e = (u,v)\<close> \<open>e' = (a,b)\<close> ab
        by (auto intro: arcs_symmetric simp: subdivide.simps)
      then have "pre_digraph.apath (subdivide G (a,b) w) x p y" "w \<noteq> y"
        using mem2 \<open>sdG.gen_iapath V x p y\<close> by (auto simp: sdG.gen_iapath_def)
      then obtain p1 p2 where p: "p = p1 @ (a,w) # (w,b) # p2"
        using exists_co_path_decomp1 \<open>(a,b) \<in> parcs G\<close> \<open>w \<notin> pverts G\<close> \<open>(a,w) \<in> set p\<close> \<open>w \<noteq> y\<close>
        by atomize_elim auto
      moreover
      from p have "co_path e w ((a,w) # (w,b) # p2) = (a,b) # co_path e w p2"
        unfolding \<open>e = (u,v)\<close> using ab by auto
      ultimately
      have "(a,b) \<in> set (co_path e w p)"
        unfolding \<open>e = (u,v)\<close> using ab \<open>u \<noteq> w\<close> \<open>v \<noteq> w\<close>
        by (induct p rule: co_path_induct) (auto simp: co_path_append)
      then show ?thesis
        using \<open>gen_iapath V x (co_path e w p) y\<close> \<open>e' = (a,b)\<close> by fast
    qed
    then show "fst e' \<noteq> snd e'" by (blast dest: no_loops_in_iapath)
  qed

  have unique: "\<forall>u v p q. (gen_iapath V u p v \<and> gen_iapath V u q v) \<longrightarrow> p = q"
  proof safe
    fix x y p q assume A: "gen_iapath V x p y" "gen_iapath V x q y"
    then have "set p \<subseteq> parcs G" "set q \<subseteq> parcs G"
      by (auto simp: gen_iapath_def apath_def)
    then have w_p: "(u,w) \<notin> set p" "(v,w) \<notin> set p" and w_q: "(u,w) \<notin> set q" "(v,w) \<notin> set q"
      using mem1 by (auto simp: wellformed')

    from A have "sdG.gen_iapath V x (sd_path e w p) y" "sdG.gen_iapath V x (sd_path e w q) y"
      using mem1 V_G by (auto intro: gen_iapath_sd_path)
    then have "sd_path e w p = sd_path e w q"
      using \<open>sdG.is_slim V\<close> unfolding sdG.is_slim_def by metis
    then have "co_path e w (sd_path e w p) = co_path e w (sd_path e w q)" by simp
    then show "p = q" using w_p w_q \<open>e = (u,v)\<close> by (simp add: co_sd_id)
  qed

  from pverts parcs V_G unique show ?thesis by (auto simp: is_slim_def)
qed

end

context pair_pseudo_graph begin

lemma subdivision_gen_contr:
  assumes "is_slim V"
  shows "subdivision_pair (gen_contr_graph G V) G"
using assms using pair_pseudo_graph
proof (induct "card (pverts G - V)" arbitrary: G)
  case 0
  interpret G: pair_pseudo_graph G by fact
  have "pair_bidirected_digraph G"
    using G.pair_sym_arcs 0 by unfold_locales (auto simp: G.is_slim_def)
  with 0 show ?case
    by (auto intro: subdivision_pair_intros simp: G.gen_contr_triv G.is_slim_def)
next
  case (Suc n)
  interpret G: pair_pseudo_graph G by fact

  from \<open>Suc n = card (pverts G - V)\<close>
  have "pverts G - V \<noteq> {}"
    by (metis Nat.diff_le_self Suc_n_not_le_n card_Diff_subset_Int diff_Suc_Suc empty_Diff finite.emptyI inf_bot_left)
  then obtain w where "w \<in> pverts G - V" by auto
  then obtain x q y where q: "G.gen_iapath V x q y" "w \<in> set (G.awalk_verts x q)" "in_degree G w \<le> 2"
    using \<open>G.is_slim V\<close> by (auto simp: G.is_slim_def)
  then have "w \<noteq> x" "w \<noteq> y" "w \<notin> V" using \<open>w \<in> pverts G - V\<close> by (auto simp: G.gen_iapath_def)
  then obtain e where "e \<in> set q" "snd e = w"
    using \<open>w \<in> pverts G - V\<close> q
    unfolding G.gen_iapath_def G.apath_def G.awalk_conv
    by (auto simp: G.awalk_verts_conv')
  moreover define u where "u = fst e"
  ultimately obtain q1 q2 v where q_decomp: "q = q1 @ (u, w) # (w, v) # q2" "u \<noteq> v" "w \<noteq> v"
    using q \<open>w \<noteq> y\<close> unfolding G.gen_iapath_def by atomize_elim (rule G.apath_succ_decomp, auto)
  with q have qi_walks: "G.awalk x q1 u" "G.awalk v q2 y"
    by (auto simp: G.gen_iapath_def G.apath_def G.awalk_Cons_iff)

  from q q_decomp have uvw_arcs1: "(u,w) \<in> parcs G" "(w,v) \<in> parcs G"
    by (auto simp: G.gen_iapath_def G.apath_def)
  then have uvw_arcs2: "(w,u) \<in> parcs G" "(v,w) \<in> parcs G"
    by (blast intro: G.arcs_symmetric)+

  have "u \<noteq> w" "v \<noteq> w" using q_decomp q
    by (auto simp: G.gen_iapath_def G.apath_append_iff G.apath_simps)

  have in_arcs: "in_arcs G w = {(u,w), (v,w)}"
  proof -
    have "{(u,w), (v,w)} \<subseteq> in_arcs G w"
      using uvw_arcs1 uvw_arcs2 by (auto simp: )
    moreover note \<open>in_degree G w \<le> 2\<close>
    moreover have "card {(u,w), (v,w)} = 2" using \<open>u \<noteq> v\<close> by auto
    ultimately
    show ?thesis by - (rule card_seteq[symmetric], auto simp: in_degree_def)
  qed
  have out_arcs: "out_arcs G w \<subseteq> {(w,u), (w,v)}" (is "?L \<subseteq> ?R")
  proof
    fix e assume "e \<in> out_arcs G w"
    then have "(snd e, fst e) \<in> in_arcs G w"
      by (auto intro: G.arcs_symmetric)
    then show "e \<in> {(w, u), (w, v)}" using in_arcs by auto
  qed

  have "(u,v) \<notin> parcs G"
  proof
    assume "(u,v) \<in> parcs G"
    have "G.gen_iapath V x (q1 @ (u,v) # q2) y"
    proof -
      have awalk': "G.awalk x (q1 @ (u,v) # q2) y"
        using qi_walks \<open>(u,v) \<in> parcs G\<close>
        by (auto simp: G.awalk_simps)

      have "G.awalk x q y" using \<open>G.gen_iapath V x q y\<close> by (auto simp: G.gen_iapath_def G.apath_def)

      have "distinct (G.awalk_verts x (q1 @ (u,v) # q2))"
        using awalk' \<open>G.gen_iapath V x q y\<close> unfolding q_decomp 
        by (auto simp: G.gen_iapath_def G.apath_def G.awalk_verts_append)
      moreover
      have "set (G.inner_verts (q1 @ (u,v) # q2)) \<subseteq> set (G.inner_verts q)"
        using awalk' \<open>G.awalk x q y\<close> unfolding q_decomp
        by (auto simp: butlast_append G.inner_verts_conv[of _ x] G.awalk_verts_append
          intro: in_set_butlast_appendI)
      then have "set (G.inner_verts (q1 @ (u,v) # q2)) \<inter> V = {}"
        using \<open>G.gen_iapath V x q y\<close> by (auto simp: G.gen_iapath_def)
      ultimately show ?thesis using awalk' \<open>G.gen_iapath V x q y\<close> by (simp add: G.gen_iapath_def G.apath_def)
    qed
    then have "(q1 @ (u,v) # q2) = q"
      using \<open>G.gen_iapath V x q y\<close> \<open>G.is_slim V\<close> unfolding G.is_slim_def by metis
    then show False unfolding q_decomp by simp
  qed
  then have "(v,u) \<notin> parcs G" by (auto intro: G.arcs_symmetric)

  define G' where "G' = \<lparr>pverts = pverts G - {w},
      parcs = {(u,v), (v,u)} \<union> (parcs G - {(u,w), (w,u), (v,w), (w,v)})\<rparr>"

  have mem_G': "(u,v) \<in> parcs G'" "w \<notin> pverts G'" by (auto simp: G'_def)

  interpret pd_G': pair_fin_digraph G'
  proof
    fix e assume A: "e \<in> parcs G'"
    have "e \<in> parcs G \<and> e \<noteq> (u, w) \<and> e \<noteq> (w, u) \<and> e \<noteq> (v, w) \<and> e \<noteq> (w, v) \<Longrightarrow> fst e \<noteq> w"
      "e \<in> parcs G \<and> e \<noteq> (u, w) \<and> e \<noteq> (w, u) \<and> e \<noteq> (v, w) \<and> e \<noteq> (w, v) \<Longrightarrow> snd e \<noteq> w"
      using out_arcs in_arcs by auto
    with A uvw_arcs1 show "fst e \<in> pverts G'" "snd e \<in> pverts G'"
      using \<open>u \<noteq> w\<close> \<open>v \<noteq> w\<close> by (auto simp: G'_def G.wellformed')
  next
  qed (auto simp: G'_def arc_to_ends_def)

  interpret spd_G': pair_pseudo_graph G'
  proof (unfold_locales, simp add: symmetric_def)
    have "sym {(u,v), (v,u)}" "sym (parcs G)" "sym {(u, w), (w, u), (v, w), (w, v)}"
      using G.sym_arcs by (auto simp: symmetric_def sym_def) 
    then have "sym ({(u,v), (v,u)} \<union> (parcs G - {(u,w), (w,u), (v,w), (w,v)}))"
      by (intro sym_Un) (auto simp: sym_diff)
    then show "sym (parcs G')" unfolding G'_def by simp
  qed

  have card_G': "n = card (pverts G' - V)"
  proof -
    have "pverts G - V = insert w (pverts G' - V)"
      using \<open>w \<in> pverts G - V\<close> by (auto simp: G'_def)
    then show ?thesis using \<open>Suc n = card (pverts G - V)\<close> mem_G' by simp
  qed

  have G_is_sd: "G = subdivide G' (u,v) w" (is "_ = ?sdG'")
    using \<open>w \<in> pverts G - V\<close> \<open>(u,v) \<notin> parcs G\<close> \<open>(v,u) \<notin> parcs G\<close>  uvw_arcs1 uvw_arcs2
    by (intro pair_pre_digraph.equality) (auto simp: G'_def)
  
  have gcg_sd: "gen_contr_graph (subdivide G' (u,v) w) V = gen_contr_graph G' V"
  proof -
    have "V \<subseteq> pverts G"
      using \<open>G.is_slim V\<close> by (auto simp: G.is_slim_def verts3_def)
    moreover
    have "verts3 G' = verts3 G"  
      by (simp only: G_is_sd spd_G'.verts3_subdivide[OF \<open>(u,v) \<in> parcs G'\<close> \<open>w \<notin> pverts G'\<close>])
    ultimately
    have V: "V \<subseteq> pverts G'"
      using \<open>w \<in> pverts G - V\<close> by (auto simp: G'_def)
    with mem_G' show ?thesis by (rule spd_G'.gcg_subdivide_eq)
  qed

  have is_slim_G': "pd_G'.is_slim V" using \<open>G.is_slim V\<close> mem_G' \<open>w \<notin> V\<close>
    unfolding G_is_sd by (rule spd_G'.is_slim_if_subdivide)
  with mem_G' have "subdivision_pair (gen_contr_graph G' V) (subdivide G' (u, v) w)"
    by (intro Suc card_G' subdivision_pair_intros) auto
  then show ?case by (simp add: gcg_sd G_is_sd)
qed

lemma  contr_is_subgraph_subdivision:
  shows "\<exists>H. subgraph (with_proj H) G \<and> subdivision_pair (contr_graph G) H"
proof -
  interpret sG: pair_graph slim by (rule pair_graph_slim)

  have "subdivision_pair (gen_contr_graph slim (verts3 G)) slim "
    by (rule sG.subdivision_gen_contr) (rule slim_is_slim)
  then show ?thesis unfolding contr_graph_slim_eq by (blast intro: subgraph_slim)
qed

theorem kuratowski_contr:
  fixes K :: "'a pair_pre_digraph"
  assumes subgraph_K: "subgraph K G"
  assumes spd_K: "pair_pseudo_graph K"
  assumes kuratowski: "K\<^bsub>3,3\<^esub> (contr_graph K) \<or> K\<^bsub>5\<^esub> (contr_graph K)"
  shows "\<not>kuratowski_planar G"
proof -
  interpret spd_K: pair_pseudo_graph K by (fact spd_K)
  obtain H where subgraph_H: "subgraph (with_proj H) K"
      and subdiv_H:"subdivision_pair (contr_graph K) H"
    by atomize_elim (rule spd_K.contr_is_subgraph_subdivision)
  have grI: "\<And>K. (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K) \<Longrightarrow> graph K"
    by (auto simp: complete_digraph_def complete_bipartite_digraph_def)
  from subdiv_H and kuratowski
  have "\<exists>K. subdivision_pair K H \<and> (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K)" by blast
  then have "\<exists>K rev_K rev_H. subdivision (K, rev_K) (H, rev_H) \<and> (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K)"
    by (auto intro: grI pair_graphI_graph)
  then show ?thesis using subgraph_H subgraph_K
    unfolding kuratowski_planar_def by (auto intro: subgraph_trans)
qed

theorem certificate_characterization:
  defines "kuratowski \<equiv> \<lambda>G :: 'a pair_pre_digraph. K\<^bsub>3,3\<^esub> G \<or> K\<^bsub>5\<^esub> G"
  shows "kuratowski (contr_graph G)
    \<longleftrightarrow> (\<exists>H. kuratowski H \<and> subdivision_pair H slim \<and> verts3 G = verts3 slim)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  interpret S: pair_graph slim by (rule pair_graph_slim)
  have "subdivision_pair (contr_graph G) slim"
  proof -
    have *: "S.is_slim (verts3 G)" by (rule slim_is_slim)
    show ?thesis using contr_graph_slim_eq S.subdivision_gen_contr[OF *] by auto
  qed
  moreover
  have "verts3 slim = verts3 G" (is "?l = ?r")
  proof safe
    fix v assume "v \<in> ?l" then show "v \<in> ?r"
      using verts_slim_in_G verts3_slim_in_verts3 by auto
  next
    fix v assume "v \<in> ?r"
    have "v \<in> verts3 (contr_graph G)"
    proof -
      have "v \<in> verts (contr_graph G)"
        using \<open>v \<in> ?r\<close> by (auto simp: verts3_def gen_contr_graph_def)
      then show ?thesis
        using \<open>?L\<close> unfolding kuratowski_def by (auto simp: verts3_K33 verts3_K5)
    qed
    then have "v \<in> verts3 (gen_contr_graph slim (verts3 G))" unfolding contr_graph_slim_eq .
    then have "2 < in_degree (gen_contr_graph slim (verts3 G)) v" 
      unfolding verts3_def by auto
    also have "\<dots> \<le> in_degree slim v"
      using \<open>v \<in> ?r\<close> verts3_slim_in_verts3 by (auto intro: S.in_degree_contr)
    finally show "v \<in> verts3 slim"
      using verts3_in_slim_G \<open>v \<in> ?r\<close> unfolding verts3_def by auto
  qed
  ultimately show ?R using \<open>?L\<close> by auto
next
  assume ?R
  then have "kuratowski (gen_contr_graph slim (verts3 G))"
    unfolding kuratowski_def 
    by (auto intro: K33_contractedI K5_contractedI)
  then show ?L unfolding contr_graph_slim_eq .
qed

definition (in pair_pre_digraph) certify :: "'a pair_pre_digraph \<Rightarrow> bool" where
  "certify cert \<equiv> let C = contr_graph cert in subgraph cert G \<and> (K\<^bsub>3,3\<^esub> C \<or> K\<^bsub>5\<^esub>C)"

theorem certify_complete:
  assumes "pair_pseudo_graph cert"
  assumes "subgraph cert G"
  assumes "\<exists>H. subdivision_pair H cert \<and> (K\<^bsub>3,3\<^esub> H \<or> K\<^bsub>5\<^esub> H)"
  shows "certify cert"
  unfolding certify_def
  using assms by (auto simp: Let_def intro: K33_contractedI K5_contractedI)

theorem certify_sound:
  assumes "pair_pseudo_graph cert"
  assumes "certify cert"
  shows" \<not>kuratowski_planar G" 
  using assms by (intro kuratowski_contr) (auto simp: certify_def Let_def)

theorem certify_characterization:
  assumes "pair_pseudo_graph cert"
  shows "certify cert \<longleftrightarrow> subgraph cert G \<and> verts3 cert = verts3 (pair_pre_digraph.slim cert)
      \<and>(\<exists>H. (K\<^bsub>3,3\<^esub> (with_proj H) \<or> K\<^bsub>5\<^esub> H) \<and> subdivision_pair H (pair_pre_digraph.slim cert))"
      (is "?L \<longleftrightarrow> ?R")
  by (auto simp only: simp_thms certify_def Let_def pair_pseudo_graph.certificate_characterization[OF assms])


end

end
