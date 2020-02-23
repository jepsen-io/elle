(* Title:  Arc_Walk.thy
   Author: Lars Noschinski, TU München
*)

theory Arc_Walk
imports
  Digraph
begin

section \<open>Arc Walks\<close>

text \<open>
  We represent a walk in a graph by the list of its arcs.
\<close>

type_synonym 'b awalk = "'b list"

context pre_digraph begin

text \<open>
  The list of vertices of a walk. The additional vertex
  argument is there to deal with the case of empty walks.
\<close>
primrec awalk_verts :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a list" where
    "awalk_verts u [] = [u]"
  | "awalk_verts u (e # es) = tail G e # awalk_verts (head G e) es"

abbreviation awhd :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a" where
  "awhd u p \<equiv> hd (awalk_verts u p)"

abbreviation awlast:: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a" where
  "awlast u p \<equiv> last (awalk_verts u p)"

text \<open>
  Tests whether a list of arcs is a consistent arc sequence,
  i.e. a list of arcs, where the head G node of each arc is
  the tail G node of the following arc.
\<close>
fun cas :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "cas u [] v = (u = v)" |
  "cas u (e # es) v = (tail G e = u \<and> cas (head G e) es v)"

lemma cas_simp:
  assumes "es \<noteq> []"
  shows "cas u es v \<longleftrightarrow> tail G (hd es) = u \<and> cas (head G (hd es)) (tl es) v"
using assms by (cases es) auto

definition awalk :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "awalk u p v \<equiv> u \<in> verts G \<and> set p \<subseteq> arcs G \<and> cas u p v"

(* XXX: rename to atrail? *)
definition (in pre_digraph) trail :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "trail u p v \<equiv> awalk u p v \<and> distinct p"

definition apath :: "'a \<Rightarrow>'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "apath u p v \<equiv> awalk u p v \<and> distinct (awalk_verts u p)"

end

subsection \<open>Basic Lemmas\<close>

lemma (in pre_digraph) awalk_verts_conv:
  "awalk_verts u p = (if p = [] then [u] else map (tail G) p @ [head G (last p)])"
by (induct p arbitrary: u) auto

lemma (in pre_digraph) awalk_verts_conv':
  assumes "cas u p v"
  shows "awalk_verts u p = (if p = [] then [u] else tail G (hd p) # map (head G) p)"
  using assms by (induct u p v rule: cas.induct) (auto simp: cas_simp)

lemma (in pre_digraph) length_awalk_verts:
  "length (awalk_verts u p) = Suc (length p)"
by (simp add: awalk_verts_conv)

lemma (in pre_digraph) awalk_verts_ne_eq:
  assumes "p \<noteq> []"
  shows "awalk_verts u p = awalk_verts v p"
using assms by (auto simp: awalk_verts_conv)

lemma (in pre_digraph) awalk_verts_non_Nil[simp]:
  "awalk_verts u p \<noteq> []"
by (simp add: awalk_verts_conv)

context wf_digraph begin

lemma
  assumes "cas u p v"
  shows awhd_if_cas: "awhd u p = u" and awlast_if_cas: "awlast u p = v"
  using assms by (induct p arbitrary: u) auto

lemma awalk_verts_in_verts:
  assumes "u \<in> verts G" "set p \<subseteq> arcs G" "v \<in> set (awalk_verts u p)"
  shows "v \<in> verts G"
  using assms by (induct p arbitrary: u) (auto intro: wellformed)

lemma
  assumes "u \<in> verts G" "set p \<subseteq> arcs G"
  shows awhd_in_verts: "awhd u p \<in> verts G"
    and awlast_in_verts: "awlast u p \<in> verts G"
using assms by (auto elim: awalk_verts_in_verts)

lemma awalk_conv:
  "awalk u p v = (set (awalk_verts u p) \<subseteq> verts G
    \<and> set p \<subseteq> arcs G
    \<and> awhd u p = u \<and> awlast u p = v \<and> cas u p v)"
unfolding awalk_def using hd_in_set[OF awalk_verts_non_Nil, of u p]
by (auto intro: awalk_verts_in_verts awhd_if_cas awlast_if_cas simp del: hd_in_set)

lemma awalkI:
  assumes "set (awalk_verts u p) \<subseteq> verts G" "set p \<subseteq> arcs G" "cas u p v"
  shows "awalk u p v"
  using assms by (auto simp: awalk_conv awhd_if_cas awlast_if_cas)

lemma awalkE[elim]:
  assumes "awalk u p v"
  obtains "set (awalk_verts u p) \<subseteq> verts G" "set p \<subseteq> arcs G" "cas u p v"
    "awhd u p = u" "awlast u p = v"
using assms by (auto simp add: awalk_conv)

lemma awalk_Nil_iff:
  "awalk u [] v \<longleftrightarrow> u = v \<and> u \<in> verts G"
unfolding awalk_def by auto

lemma trail_Nil_iff:
  "trail u [] v \<longleftrightarrow> u = v \<and> u \<in> verts G"
  by (auto simp: trail_def awalk_Nil_iff)

lemma apath_Nil_iff: "apath u [] v \<longleftrightarrow> u = v \<and> u \<in> verts G"
  by (auto simp: apath_def awalk_Nil_iff)

lemma awalk_hd_in_verts: "awalk u p v \<Longrightarrow> u \<in> verts G"
  by (cases p) auto

lemma awalk_last_in_verts: "awalk u p v \<Longrightarrow> v \<in> verts G"
  unfolding awalk_conv by auto

lemma hd_in_awalk_verts:
  "awalk u p v \<Longrightarrow> u \<in> set (awalk_verts u p)"
  "apath u p v \<Longrightarrow> u \<in> set (awalk_verts u p)"
  by (case_tac [!]p) (auto simp: apath_def)

lemma awalk_Cons_iff:
  "awalk u (e # es) w \<longleftrightarrow> e \<in> arcs G \<and> u = tail G e \<and> awalk (head G e) es w"
  by (auto simp: awalk_def)

lemma trail_Cons_iff:
  "trail u (e # es ) w \<longleftrightarrow> e \<in> arcs G \<and> u = tail G e \<and> e \<notin> set es \<and> trail (head G e) es w"
  by (auto simp: trail_def awalk_Cons_iff)

lemma apath_Cons_iff:
  "apath u (e # es) w \<longleftrightarrow> e \<in> arcs G \<and> tail G e = u \<and> apath (head G e) es w
    \<and> tail G e \<notin> set (awalk_verts (head G e) es)" (is "?L \<longleftrightarrow> ?R")
by (auto simp: apath_def awalk_Cons_iff)

lemmas awalk_simps = awalk_Nil_iff awalk_Cons_iff
lemmas trail_simps = trail_Nil_iff trail_Cons_iff
lemmas apath_simps = apath_Nil_iff apath_Cons_iff

lemma arc_implies_awalk:
  "e \<in> arcs G \<Longrightarrow> awalk (tail G e) [e] (head G e)"
by (simp add: awalk_simps)

lemma apath_nonempty_ends:
  assumes "apath u p v"
  assumes "p \<noteq> []"
  shows "u \<noteq> v"
using assms
proof (induct p arbitrary: u)
  case (Cons e es)
  then have "apath (head G e) es v" "u \<notin> set (awalk_verts (head G e) es)"
    by (auto simp: apath_Cons_iff)
  moreover then have "v \<in> set (awalk_verts (head G e) es)" by (auto simp: apath_def)
  ultimately show "u \<noteq> v" by auto
qed simp



(* replace by awalk_Cons_iff?*)
lemma awalk_ConsI:
  assumes "awalk v es w"
  assumes "e \<in> arcs G" and "arc_to_ends G e = (u,v)"
  shows "awalk u (e # es) w"
  using assms by (cases es) (auto simp: awalk_def arc_to_ends_def)

lemma (in pre_digraph) awalkI_apath:
  assumes "apath u p v" shows "awalk u p v"
using assms by (simp add: apath_def)

lemma arcE:
  assumes "arc e (u,v)"
  assumes "\<lbrakk>e \<in> arcs G; tail G e = u; head G e = v\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: arc_def)

lemma in_arcs_imp_in_arcs_ends:
  assumes "e \<in> arcs G"
  shows "(tail G e, head G e) \<in> arcs_ends G"
using assms by (auto simp: arcs_ends_conv)

lemma set_awalk_verts_cas:
  assumes "cas u p v"
  shows "set (awalk_verts u p) = {u} \<union> set (map (tail G) p) \<union> set (map (head G) p)"
using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by simp
next
  case (Cons e es)
  then have "set (awalk_verts (head G e) es)
      = {head G e} \<union> set (map (tail G) es) \<union> set (map (head G) es)"
    by (auto simp: awalk_Cons_iff)
  with Cons.prems show ?case by auto
qed

lemma set_awalk_verts_not_Nil_cas:
  assumes "cas u p v" "p \<noteq> []"
  shows "set (awalk_verts u p) = set (map (tail G) p) \<union> set (map (head G) p)"
proof -
  have "u \<in> set (map (tail G) p)" using assms by (cases p) auto
  with assms show ?thesis  by (auto simp: set_awalk_verts_cas)
qed

lemma set_awalk_verts:
  assumes "awalk u p v"
  shows "set (awalk_verts u p) = {u} \<union> set (map (tail G) p) \<union> set (map (head G) p)"
  using assms by (intro set_awalk_verts_cas) blast

lemma set_awalk_verts_not_Nil:
  assumes "awalk u p v" "p \<noteq> []"
  shows "set (awalk_verts u p) = set (map (tail G) p) \<union> set (map (head G) p)"
  using assms by (intro set_awalk_verts_not_Nil_cas) blast

lemma
  awhd_of_awalk: "awalk u p v \<Longrightarrow> awhd u p = u" and
  awlast_of_awalk: "awalk u p v \<Longrightarrow> NOMATCH (awlast u p) v \<Longrightarrow> awlast u p = v"
  unfolding NOMATCH_def by auto
lemmas awends_of_awalk[simp] = awhd_of_awalk awlast_of_awalk

lemma awalk_verts_arc1:
  assumes "e \<in> set p"
  shows "tail G e \<in> set (awalk_verts u p)"
using assms by (auto simp: awalk_verts_conv)

lemma awalk_verts_arc2:
  assumes "awalk u p v" "e \<in> set p"
  shows "head G e \<in> set (awalk_verts u p)"
using assms by (simp add: set_awalk_verts)

lemma awalk_induct_raw[case_names Base Cons(*, induct pred: awalk*)]:
  assumes "awalk u p v"
  assumes "\<And>w1. w1 \<in> verts G \<Longrightarrow> P w1 [] w1"
  assumes "\<And>w1 w2 e es. e \<in> arcs G \<Longrightarrow> arc_to_ends G e = (w1, w2)
    \<Longrightarrow> P w2 es v \<Longrightarrow> P w1 (e # es) v"
  shows "P u p v"
using assms
proof (induct p arbitrary: u v)
  case Nil then show ?case using Nil.prems by auto
next
  case (Cons e es)
  from Cons.prems(1) show ?case
    by (intro Cons) (auto intro: Cons(2-) simp: arc_to_ends_def awalk_Cons_iff)
qed





subsection \<open>Appending awalks\<close>

lemma (in pre_digraph) cas_append_iff[simp]:
  "cas u (p @ q) v \<longleftrightarrow> cas u p (awlast u p) \<and> cas (awlast u p) q v"
by (induct u p v rule: cas.induct) auto

lemma cas_ends:
  assumes "cas u p v" "cas u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
using assms by (induct u p v arbitrary: u u' rule: cas.induct) auto

lemma awalk_ends:
  assumes "awalk u p v" "awalk u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
using assms by (simp add: awalk_def cas_ends)

lemma awalk_ends_eqD:
  assumes "awalk u p u" "awalk v p w"
  shows "v = w"
using awalk_ends[OF assms(1,2)] by auto

lemma awalk_empty_ends:
  assumes "awalk u [] v"
  shows "u = v"
using assms by (auto simp: awalk_def)

lemma apath_ends:
 assumes "apath u p v" and "apath u' p v'"
  shows "(p \<noteq> [] \<and> u \<noteq> v \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
using assms unfolding apath_def by (metis assms(2) apath_nonempty_ends  awalk_ends)

lemma awalk_append_iff[simp]:
  "awalk u (p @ q) v \<longleftrightarrow> awalk u p (awlast u p) \<and> awalk (awlast u p) q v" (is "?L \<longleftrightarrow> ?R")
by (auto simp: awalk_def intro: awlast_in_verts)

lemma awlast_append:
  "awlast u (p @ q) = awlast (awlast u p) q"
by (simp add: awalk_verts_conv)

lemma awhd_append:
  "awhd u (p @ q) = awhd (awhd u q) p"
by (simp add: awalk_verts_conv)

declare awalkE[rule del]

lemma awalkE'[elim]:
  assumes "awalk u p v"
  obtains "set (awalk_verts u p) \<subseteq> verts G" "set p \<subseteq> arcs G" "cas u p v"
    "awhd u p = u" "awlast u p = v" "u \<in> verts G" "v \<in> verts G"
proof -
  have "u \<in> set (awalk_verts u p)" "v \<in> set (awalk_verts u p)"
    using assms by (auto simp: hd_in_awalk_verts elim: awalkE)
  then show ?thesis using assms by (auto elim: awalkE intro: that)
qed

lemma awalk_appendI:
  assumes "awalk u p v"
  assumes "awalk v q w"
  shows "awalk u (p @ q) w"
using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by auto
next
  case (Cons e es)
  from Cons.prems have ee_e: "arc_to_ends G e = (u, head G e)"
    unfolding arc_to_ends_def by auto

  have "awalk (head G e) es v"
    using ee_e Cons(2) awalk_Cons_iff by auto
  then show ?case using Cons ee_e by (auto simp: awalk_Cons_iff)
qed

lemma awalk_verts_append_cas:
  assumes "cas u (p @ q) v"
  shows "awalk_verts u (p @ q) = awalk_verts u p @ tl (awalk_verts (awlast u p) q)"
  using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by (cases q) auto
qed (auto simp: awalk_Cons_iff)

lemma awalk_verts_append:
  assumes "awalk u (p @ q) v"
  shows "awalk_verts u (p @ q) = awalk_verts u p @ tl (awalk_verts (awlast u p) q)"
  using assms by (intro awalk_verts_append_cas) blast

lemma awalk_verts_append2:
  assumes "awalk u (p @ q) v"
  shows "awalk_verts u (p @ q) = butlast (awalk_verts u p) @ awalk_verts (awlast u p) q"
 using assms by (auto simp: awalk_verts_conv)

lemma apath_append_iff:
  "apath u (p @ q) v \<longleftrightarrow> apath u p (awlast u p) \<and> apath (awlast u p) q v \<and>
    set (awalk_verts u p) \<inter> set (tl (awalk_verts (awlast u p) q)) = {}" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have "distinct (awalk_verts (awlast u p) q)" by (auto simp: apath_def awalk_verts_append2)
  with \<open>?L\<close> show ?R by (auto simp: apath_def awalk_verts_append)
next
  assume ?R
  then show ?L by (auto simp: apath_def awalk_verts_append dest: distinct_tl)
qed

lemma (in wf_digraph) set_awalk_verts_append_cas:
  assumes "cas u p v" "cas v q w"
  shows "set (awalk_verts u (p @ q)) = set (awalk_verts u p) \<union> set (awalk_verts v q)"
proof -
  from assms have cas_pq: "cas u (p @ q) w"
    by (simp add: awlast_if_cas)
  moreover
  from assms have "v \<in> set (awalk_verts u p)"
    by (metis awalk_verts_non_Nil awlast_if_cas last_in_set)
  ultimately show ?thesis using assms
    by (auto simp: set_awalk_verts_cas)
qed

lemma (in wf_digraph) set_awalk_verts_append:
  assumes "awalk u p v" "awalk v q w"
  shows "set (awalk_verts u (p @ q)) = set (awalk_verts u p) \<union> set (awalk_verts v q)"
proof -
  from assms have "awalk u (p @ q) w" by auto
  moreover
  with assms have "v \<in> set (awalk_verts u (p @ q))"
    by (auto simp: awalk_verts_append)
  ultimately show ?thesis using assms
    by (auto simp: set_awalk_verts)
qed

lemma cas_takeI:
  assumes "cas u p v" "awlast u (take n p) = v'"
  shows "cas u (take n p) v'"
proof -
  from assms have "cas u (take n p @ drop n p) v" by simp
  with assms show ?thesis unfolding cas_append_iff by simp
qed

lemma cas_dropI:
  assumes "cas u p v" "awlast u (take n p) = u'"
  shows "cas u' (drop n p) v"
proof -
  from assms have "cas u (take n p @ drop n p) v" by simp
  with assms show ?thesis unfolding cas_append_iff by simp
qed

lemma awalk_verts_take_conv:
  assumes "cas u p v"
  shows "awalk_verts u (take n p) = take (Suc n) (awalk_verts u p)"
proof -
  from assms have "cas u (take n p) (awlast u (take n p))" by (auto intro: cas_takeI)
  with assms show ?thesis
    by (cases n p rule: nat.exhaust[case_product list.exhaust])
       (auto simp: awalk_verts_conv' take_map simp del: awalk_verts.simps)
qed

lemma awalk_verts_drop_conv:
  assumes "cas u p v"
  shows "awalk_verts u' (drop n p) = (if n < length p then drop n (awalk_verts u p) else [u'])"
using assms by (auto simp: awalk_verts_conv drop_map)

lemma awalk_decomp_verts:
  assumes cas: "cas u p v" and ev_decomp: "awalk_verts u p = xs @ y # ys"
  obtains q r where "cas u q y" "cas y r v" "p = q @ r" "awalk_verts u q = xs @ [y]" "awalk_verts y r = y # ys"
using assms
proof -
  define q r where "q = take (length xs) p" and "r = drop (length xs) p"
  then have p: "p = q @ r" by simp
  moreover from p have "cas u q (awlast u q)" "cas (awlast u q) r v"
    using \<open>cas u p v\<close> by auto
  moreover have "awlast u q = y"
    using q_def and assms by (auto simp: awalk_verts_take_conv)
  moreover have *: "awalk_verts u q = xs @ [awlast u q]"
    using assms q_def by (auto simp: awalk_verts_take_conv)
  moreover from * have "awalk_verts y r = y # ys"
    unfolding q_def r_def using assms by (auto simp: awalk_verts_drop_conv not_less)
  ultimately show ?thesis by (intro that) auto
qed

lemma awalk_decomp:
  assumes "awalk u p v"
  assumes "w \<in> set (awalk_verts u p)"
  shows "\<exists>q r. p = q @ r \<and> awalk u q w \<and> awalk w r v"
proof -
  from assms have "cas u p v" by auto
  moreover from assms obtain xs ys where
    "awalk_verts u p = xs @ w # ys" by (auto simp: in_set_conv_decomp)
  ultimately
  obtain q r where "cas u q w" "cas w r v" "p = q @ r" "awalk_verts u q = xs @ [w]"
    by (auto intro: awalk_decomp_verts)
  with assms show ?thesis by auto
qed


lemma awalk_not_distinct_decomp:
  assumes "awalk u p v"
  assumes "\<not> distinct (awalk_verts u p)"
  shows "\<exists>q r s. p = q @ r @ s \<and> distinct (awalk_verts u q)
    \<and> 0 < length r
    \<and> (\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v)"
proof -
  from assms
  obtain xs ys zs y where
    pv_decomp: "awalk_verts u p = xs @ y # ys @ y # zs"
    and xs_y_props: "distinct xs" "y \<notin> set xs" "y \<notin> set ys"
    using not_distinct_decomp_min_prefix by blast

  obtain q p' where "cas u q y" "p = q @ p'" "awalk_verts u q = xs @ [y]"
    and p'_props: "cas y p' v"  "awalk_verts y p' = (y # ys) @ y # zs"
    using assms pv_decomp by - (rule awalk_decomp_verts, auto)
  obtain r s where "cas y r y" "cas y s v" "p' = r @ s"
    "awalk_verts y r = y # ys @ [y]" "awalk_verts y s = y # zs"
    using p'_props by (rule awalk_decomp_verts) auto

  have "p = q @ r @ s" using \<open>p = q @ p'\<close> \<open>p' = r @ s\<close> by simp
  moreover
  have "distinct (awalk_verts u q)" using \<open>awalk_verts u q = xs @ [y]\<close> and xs_y_props  by simp
  moreover
  have "0 < length r" using \<open>awalk_verts y r = y # ys @ [y]\<close> by auto
  moreover
  from pv_decomp assms have "y \<in> verts G" by auto
  then have "awalk u q y" "awalk y r y" "awalk y s v"
    using \<open>awalk u p v\<close> \<open>cas u q y\<close> \<open>cas y r y\<close> \<open>cas y s v\<close> unfolding \<open>p = q @ r @ s\<close>
    by (auto simp: awalk_def)
  ultimately show ?thesis by blast
qed

lemma apath_decomp_disjoint:
  assumes "apath u p v"
  assumes "p = q @ r"
  assumes "x \<in> set (awalk_verts u q)" "x \<in> set (tl (awalk_verts (awlast u q) r))"
  shows False
using assms by (auto simp: apath_def awalk_verts_append)



subsection \<open>Cycles\<close>

definition closed_w :: "'b awalk \<Rightarrow> bool" where
  "closed_w p \<equiv> \<exists>u. awalk u p u \<and> 0 < length p"

text \<open>
  The definitions of cycles in textbooks vary w.r.t to the minimial length
  of a cycle.

  The definition given here matches \cite{diestel2010graph}.
  \cite{bangjensen2009digraphs} excludes loops from being cycles.
  Volkmann (Lutz Volkmann: Graphen an allen Ecken und Kanten, 2006 (?))
  places no restriction on the length in the definition, but later
  usage assumes cycles to be non-empty.
\<close>
definition (in pre_digraph) cycle :: "'b awalk \<Rightarrow> bool" where
  "cycle p \<equiv> \<exists>u. awalk u p u \<and> distinct (tl (awalk_verts u p)) \<and> p \<noteq> []"

lemma cycle_altdef:
  "cycle p \<longleftrightarrow> closed_w p \<and> (\<exists>u. distinct (tl (awalk_verts u p)))"
by (cases p) (auto simp: closed_w_def cycle_def)

lemma (in wf_digraph) distinct_tl_verts_imp_distinct:
  assumes "awalk u p v"
  assumes "distinct (tl (awalk_verts u p))"
  shows "distinct p"
proof (rule ccontr)
  assume "\<not>distinct p"
  then obtain e xs ys zs where p_decomp: "p = xs @ e # ys @ e # zs"
    by (blast dest: not_distinct_decomp_min_prefix)
  then show False
    using assms p_decomp by (auto simp: awalk_verts_append awalk_Cons_iff set_awalk_verts)
qed

lemma (in wf_digraph) distinct_verts_imp_distinct:
  assumes "awalk u p v"
  assumes "distinct (awalk_verts u p)"
  shows "distinct p"
  using assms by (blast intro: distinct_tl_verts_imp_distinct distinct_tl)

lemma (in wf_digraph) cycle_conv:
  "cycle p \<longleftrightarrow> (\<exists>u. awalk u p u \<and> distinct (tl (awalk_verts u p)) \<and> distinct p \<and> p \<noteq> [])"
  unfolding cycle_def by (auto intro: distinct_tl_verts_imp_distinct)

lemma (in loopfree_digraph) cycle_digraph_conv:
  "cycle p \<longleftrightarrow> (\<exists>u. awalk u p u \<and> distinct (tl (awalk_verts u p)) \<and> 2 \<le> length p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume "cycle p"
  then obtain u where *: "awalk u p u" "distinct (tl (awalk_verts u p))" "p \<noteq> []"
    unfolding cycle_def by auto
  have "2 \<le> length p"
  proof (rule ccontr)
    assume "\<not>?thesis" with * obtain e where "p=[e]"
      by (cases p) (auto simp: not_le)
    then show False using * by (auto simp: awalk_simps dest: no_loops)
  qed
  then show ?R using * by auto
qed (auto simp: cycle_def)

lemma (in wf_digraph) closed_w_imp_cycle:
  assumes "closed_w p" shows "\<exists>p. cycle p"
  using assms
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  then obtain u where *: "awalk u p u" "p \<noteq> []" by (auto simp: closed_w_def)
  show ?thesis
  proof cases
    assume "distinct (tl (awalk_verts u p))"
    with less show ?thesis by (auto simp: closed_w_def cycle_altdef)
  next
    assume A: "\<not>distinct (tl (awalk_verts u p))"
    then obtain e es where "p = e # es" by (cases p) auto
    with A * have **: "awalk (head G e) es u" "\<not>distinct (awalk_verts (head G e) es)"
      by (auto simp: awalk_Cons_iff)
    obtain q r s where "es = q @ r @ s" "\<exists>w. awalk w r w" "closed_w r"
      using awalk_not_distinct_decomp[OF **] by (auto simp: closed_w_def)
    then have "length r < length p" using \<open>p = _\<close> by auto
    then show ?thesis using \<open>closed_w r\<close> by (rule less)
  qed
qed



subsection \<open>Reachability\<close>

lemma reachable1_awalk:
  "u \<rightarrow>\<^sup>+ v \<longleftrightarrow> (\<exists>p. awalk u p v \<and> p \<noteq> [])"
proof
  assume "u \<rightarrow>\<^sup>+ v" then show "\<exists>p. awalk u p v \<and> p \<noteq> []"
  proof (induct rule: converse_trancl_induct)
    case (base y) then obtain e where "e \<in> arcs G" "tail G e = y" "head G e = v" by auto
    with arc_implies_awalk show ?case by auto
  next
    case (step x y)
    then obtain p where "awalk y p v" "p \<noteq> []" by auto
    moreover
    from \<open>x \<rightarrow> y\<close> obtain e where "tail G e = x" "head G e = y" "e \<in> arcs G"
      by auto
    ultimately
    have "awalk x (e # p) v"
      by (auto simp: awalk_Cons_iff)
    then show ?case by auto
  qed
next
  assume "\<exists>p. awalk u p v \<and> p \<noteq> []" then obtain p where "awalk u p v" "p \<noteq> []" by auto
  thus "u \<rightarrow>\<^sup>+ v"
  proof (induct p arbitrary: u)
    case (Cons a as) then show ?case
      by (cases "as = []") (auto simp: awalk_simps trancl_into_trancl2 dest: in_arcs_imp_in_arcs_ends)
  qed simp
qed

lemma reachable_awalk:
  "u \<rightarrow>\<^sup>* v \<longleftrightarrow> (\<exists>p. awalk u p v)"
proof cases
  assume "u = v"
  have "u \<rightarrow>\<^sup>*u \<longleftrightarrow> awalk u [] u" by (auto simp: awalk_Nil_iff reachable_in_verts)
  also have "\<dots> \<longleftrightarrow> (\<exists>p. awalk u p u)"
    by (metis awalk_Nil_iff awalk_hd_in_verts)
  finally show ?thesis using \<open>u = v\<close> by simp
next
  assume "u \<noteq> v"
  then have "u \<rightarrow>\<^sup>* v \<longleftrightarrow> u \<rightarrow>\<^sup>+ v" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>p. awalk u p v)"
    using \<open>u \<noteq> v\<close> unfolding reachable1_awalk by force
  finally show ?thesis .
qed

lemma reachable_awalkI[intro?]:
  assumes "awalk u p v"
  shows "u \<rightarrow>\<^sup>* v"
  unfolding reachable_awalk using assms by auto

lemma reachable1_awalkI:
  "awalk v p w \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v \<rightarrow>\<^sup>+ w"
by (auto simp add: reachable1_awalk)


lemma reachable_arc_trans:
  assumes "u \<rightarrow>\<^sup>* v" "arc e (v,w)"
  shows "u \<rightarrow>\<^sup>* w"
proof -
  from \<open>u \<rightarrow>\<^sup>* v\<close> obtain p where "awalk u p v"
    by (auto simp: reachable_awalk)
  moreover have "awalk v [e] w"
    using \<open>arc e (v,w)\<close>
    by (auto simp: arc_def awalk_def)
  ultimately have "awalk u (p @ [e]) w"
    by (rule awalk_appendI)
  then show ?thesis ..
qed

lemma awalk_verts_reachable_from:
  assumes "awalk u p v" "w \<in> set (awalk_verts u p)" shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w"
proof  -
  obtain s where "awalk u s w" using awalk_decomp[OF assms] by blast
  then show ?thesis by (metis reachable_awalk)
qed

lemma awalk_verts_reachable_to:
  assumes "awalk u p v" "w \<in> set (awalk_verts u p)" shows "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
proof  -
  obtain s where "awalk w s v" using awalk_decomp[OF assms] by blast
  then show ?thesis by (metis reachable_awalk)
qed





subsection \<open>Paths\<close>

lemma (in fin_digraph) length_apath_less:
  assumes "apath u p v"
  shows "length p < card (verts G)"
proof -
  have "length p < length (awalk_verts u p)" unfolding awalk_verts_conv
    by (auto simp: awalk_verts_conv)
  also have "length (awalk_verts u p) = card (set (awalk_verts u p))"
    using \<open>apath u p v\<close> by (auto simp: apath_def distinct_card)
  also have "\<dots> \<le> card (verts G)"
    using \<open>apath u p v\<close> unfolding apath_def awalk_conv
    by (auto intro: card_mono)
  finally show ?thesis .
qed

lemma (in fin_digraph) length_apath:
  assumes "apath u p v"
  shows "length p \<le> card (verts G)"
  using length_apath_less[OF assms] by auto

lemma (in fin_digraph) apaths_finite_triple:
  shows "finite {(u,p,v). apath u p v}"
proof -
  have "\<And>u p v. awalk u p v \<Longrightarrow> distinct (awalk_verts u p) \<Longrightarrow>length p \<le> card (verts G)"
    by (rule length_apath) (auto simp: apath_def)
  then have "{(u,p,v). apath u p v} \<subseteq> verts G \<times> {es. set es \<subseteq> arcs G \<and> length es \<le> card (verts G)} \<times> verts G"
    by (auto simp: apath_def)
  moreover have "finite ..."
    using finite_verts finite_arcs
    by (intro finite_cartesian_product finite_lists_length_le)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma (in fin_digraph) apaths_finite:
  shows "finite {p. apath u p v}"
proof -
  have "{p. apath u p v} \<subseteq> (fst o snd) ` {(u,p,v). apath u p v}"
    by force
  with apaths_finite_triple show ?thesis  by (rule finite_surj)
qed

fun is_awalk_cyc_decomp :: "'b awalk =>
  ('b awalk \<times> 'b awalk \<times> 'b awalk) \<Rightarrow> bool" where
  "is_awalk_cyc_decomp p (q,r,s) \<longleftrightarrow> p = q @ r @ s
    \<and> (\<exists>u v w. awalk u q v \<and> awalk v r v \<and> awalk v s w)
    \<and> 0 <length r
    \<and> (\<exists>u. distinct (awalk_verts u q))"

definition awalk_cyc_decomp :: "'b awalk
    \<Rightarrow> 'b awalk \<times> 'b awalk \<times> 'b awalk" where
  "awalk_cyc_decomp p = (SOME qrs. is_awalk_cyc_decomp p qrs)"

function awalk_to_apath :: "'b awalk \<Rightarrow> 'b awalk" where
  "awalk_to_apath p = (if \<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk u p v)
     then (let (q,r,s) = awalk_cyc_decomp p in awalk_to_apath (q @ s))
     else p)"
by auto

lemma awalk_cyc_decomp_has_prop:
  assumes "awalk u p v" and "\<not>distinct (awalk_verts u p)"
  shows "is_awalk_cyc_decomp p (awalk_cyc_decomp p)"
proof -
  obtain q r s where *: "p = q @ r @ s \<and> distinct (awalk_verts u q)
      \<and> 0 < length r
      \<and> (\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v)"
    by (atomize_elim) (rule awalk_not_distinct_decomp[OF assms])
  then have "\<exists>x. is_awalk_cyc_decomp p x"
    by (intro exI[where x="(q,r,s)"]) auto
  then show ?thesis unfolding awalk_cyc_decomp_def ..
qed

lemma awalk_cyc_decompE:
  assumes dec: "awalk_cyc_decomp p = (q,r,s)"
  assumes p_props: "awalk u p v" "\<not>distinct (awalk_verts u p)"
  obtains "p = q @ r @ s" "distinct (awalk_verts u q)" "\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v" "closed_w r"
proof
  show "p = q @ r @ s" "distinct (awalk_verts u q)" "closed_w r"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec
    by (auto simp: closed_w_def awalk_verts_conv)
  then have "p \<noteq> []" by (auto simp: closed_w_def)

  (* TODO: Can we find some general rules to prove the last property?*)
  obtain u' w' v' where obt_awalk: "awalk u' q w'" "awalk w' r w'" "awalk w' s v'"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec by auto
  then have "awalk u' p v'"
    using \<open>p = q @ r @ s\<close> by simp
  then have "u = u'" and "v = v'" using \<open>p \<noteq> []\<close> \<open>awalk u p v\<close> by (metis awalk_ends)+
  then have "awalk u q w'" "awalk w' r w'" "awalk w' s v"
    using obt_awalk by auto
  then show "\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v" by auto
qed

lemma awalk_cyc_decompE':
  assumes p_props: "awalk u p v" "\<not>distinct (awalk_verts u p)"
  obtains q r s where "p = q @ r @ s" "distinct (awalk_verts u q)" "\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v" "closed_w r"
proof -
  obtain q r s where "awalk_cyc_decomp p = (q,r,s)"
    by (cases "awalk_cyc_decomp p") auto
  then have "p = q @ r @ s" "distinct (awalk_verts u q)" "\<exists>w. awalk u q w \<and> awalk w r w \<and> awalk w s v" "closed_w r"
    using assms by (auto elim: awalk_cyc_decompE)
  then show ?thesis ..
qed

termination awalk_to_apath
proof (relation "measure length")
  fix G p qrs rs q r s

  have X: "\<And>x y. closed_w r \<Longrightarrow> awalk x r y \<Longrightarrow> x = y"
    unfolding closed_w_def by (blast dest: awalk_ends)

  assume "\<not>(\<exists>u. distinct (awalk_verts u p)) \<and>(\<exists>u v. awalk u p v)"
    and **:"qrs = awalk_cyc_decomp p" "(q, rs) = qrs" "(r, s) = rs"
  then obtain u v where *: "awalk u p v" "\<not>distinct (awalk_verts u p)"
    by (cases p) auto
  then have "awalk_cyc_decomp p = (q,r,s)" using ** by simp
  then have "is_awalk_cyc_decomp p (q,r,s)"
    apply (rule awalk_cyc_decompE[OF _ *])
    using X[of "awlast u q"  "awlast (awlast u q) r"] *(1)
    by (auto simp: closed_w_def)
  then show "(q @ s, p) \<in> measure length"
    by (auto simp: closed_w_def)
qed simp
declare awalk_to_apath.simps[simp del]

lemma awalk_to_apath_induct[consumes 1, case_names path decomp]:
  assumes awalk: "awalk u p v"
  assumes dist: "\<And>p. awalk u p v \<Longrightarrow> distinct (awalk_verts u p) \<Longrightarrow> P p"
  assumes dec: "\<And>p q r s. \<lbrakk>awalk u p v; awalk_cyc_decomp p = (q,r,s);
    \<not>distinct (awalk_verts u p); P (q @ s)\<rbrakk> \<Longrightarrow> P p"
  shows "P p"
using awalk
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct (awalk_verts u p)")
    case True then show ?thesis by (auto intro: dist less.prems)
  next
    case False
    obtain q r s where p_cdecomp: "awalk_cyc_decomp p = (q,r,s)"
      by (cases "awalk_cyc_decomp p") auto
    then have "is_awalk_cyc_decomp p (q,r,s)" "p = q @ r @ s"
      using awalk_cyc_decomp_has_prop[OF less.prems(1) False] by auto
    then have "length (q @ s) < length p" "awalk u (q @ s) v"
      using less.prems by (auto dest!: awalk_ends_eqD)
    then have "P (q @ s)" by (auto intro: less)

    with p_cdecomp False show ?thesis by (auto intro: dec less.prems)
  qed
qed

lemma step_awalk_to_apath:
  assumes awalk: "awalk u p v"
    and decomp: "awalk_cyc_decomp p = (q, r, s)"
    and dist: "\<not> distinct (awalk_verts u p)"
  shows "awalk_to_apath p = awalk_to_apath (q @ s)"
proof -
  from dist have "\<not>(\<exists>u. distinct (awalk_verts u p))"
    by (auto simp: awalk_verts_conv)
  with awalk and decomp show "awalk_to_apath p = awalk_to_apath (q @ s)"
    by (auto simp: awalk_to_apath.simps)
qed

lemma apath_awalk_to_apath:
  assumes "awalk u p v"
  shows "apath u (awalk_to_apath p) v"
using assms
proof (induct rule: awalk_to_apath_induct)
  case (path p)
  then have "awalk_to_apath p = p"
    by (auto simp: awalk_to_apath.simps)
  then show ?case using path by (auto simp: apath_def)
next
  case (decomp p q r s)
  then show ?case using step_awalk_to_apath[of _ p _ q r s] by simp
qed

lemma (in wf_digraph) awalk_to_apath_subset:
  assumes "awalk u p v"
  shows "set (awalk_to_apath p) \<subseteq> set p"
using assms
proof (induct rule: awalk_to_apath_induct)
  case (path p)
  then have "awalk_to_apath p = p"
    by (auto simp: awalk_to_apath.simps)
  then show ?case by simp
next
  case (decomp p q r s)
  have *: "\<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk u p v)"
    using decomp by (cases p) auto
  have "set (awalk_to_apath (q @ s)) \<subseteq> set p"
    using decomp by (auto elim!: awalk_cyc_decompE)
  then
  show ?case by (subst awalk_to_apath.simps) (simp only: * simp_thms if_True decomp Let_def prod.simps)
qed

lemma reachable_apath:
  "u \<rightarrow>\<^sup>* v \<longleftrightarrow> (\<exists>p. apath u p v)"
  by (auto intro: awalkI_apath apath_awalk_to_apath simp: reachable_awalk)

lemma no_loops_in_apath:
  assumes "apath u p v" "a \<in> set p" shows "tail G a \<noteq> head G a"
proof -
  from \<open>a \<in> set p\<close> obtain p1 p2 where "p = p1 @ a # p2" by (auto simp: in_set_conv_decomp)
  with \<open>apath u p v\<close> have "apath (tail G a) ([a] @ p2) (v)"
    by (auto simp: apath_append_iff apath_Cons_iff apath_Nil_iff)
  then have "apath (tail G a) [a] (head G a)" by - (drule apath_append_iff[THEN iffD1], simp)
  then show ?thesis by (auto simp:  apath_Cons_iff)
qed


end

end
