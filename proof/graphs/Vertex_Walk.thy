(* Title:  Vertex_Walk.thy
   Author: Lars Noschinski, TU München
*)

theory Vertex_Walk
imports Arc_Walk
begin

section \<open>Walks Based on Vertices\<close>

text \<open>
  These definitions are here mainly for historical purposes, as they
  do not really work with multigraphs. Consider using Arc Walks
  instead.
\<close>

type_synonym 'a vwalk = "'a list"

text \<open>Computes the list of arcs belonging to a list of nodes\<close>
fun vwalk_arcs :: "'a vwalk \<Rightarrow> ('a \<times> 'a) list" where
    "vwalk_arcs [] = []"
  | "vwalk_arcs [x] = []"
  | "vwalk_arcs (x#y#xs) = (x,y) # vwalk_arcs (y#xs)"

definition vwalk_length :: "'a vwalk \<Rightarrow> nat" where
  "vwalk_length p \<equiv> length (vwalk_arcs p)"

lemma vwalk_length_simp[simp]:
  shows "vwalk_length p = length p - 1"
by (induct p rule: vwalk_arcs.induct) (auto simp: vwalk_length_def)

definition vwalk :: "'a vwalk \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "vwalk p G \<equiv> set p \<subseteq> verts G \<and> set (vwalk_arcs p) \<subseteq> arcs_ends G \<and> p \<noteq> []"

definition vpath :: "'a vwalk \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "vpath p G \<equiv> vwalk p G \<and> distinct p"

text \<open>For a given vwalk, compute a vpath with the same tail G and end\<close>
function vwalk_to_vpath :: "'a vwalk \<Rightarrow> 'a vwalk" where
    "vwalk_to_vpath [] = []"
  | "vwalk_to_vpath (x # xs) = (if (x \<in> set xs)
      then vwalk_to_vpath (dropWhile (\<lambda>y. y \<noteq> x) xs)
      else x # vwalk_to_vpath xs)"
by pat_completeness auto
termination by (lexicographic_order simp add: length_dropWhile_le)


lemma vwalkI[intro]:
  assumes "set p \<subseteq> verts G"
  assumes "set (vwalk_arcs p) \<subseteq> arcs_ends G"
  assumes "p \<noteq> []"
  shows "vwalk p G"
using assms by (auto simp add: vwalk_def)

lemma vwalkE[elim]:
  assumes "vwalk p G"
  assumes "set p \<subseteq> verts G \<Longrightarrow>
    set (vwalk_arcs p) \<subseteq> arcs_ends G \<and> p \<noteq> [] \<Longrightarrow> P"
  shows "P"
using assms by (simp add: vwalk_def)

lemma vpathI[intro]:
  assumes "vwalk p G"
  assumes "distinct p"
  shows "vpath p G"
using assms by (simp add: vpath_def)

lemma vpathE[elim]:
  assumes "vpath p G"
  assumes "vwalk p G \<Longrightarrow> distinct p \<Longrightarrow> P"
  shows "P"
using assms by (simp add: vpath_def)


lemma vwalk_consI:
  assumes "vwalk p G"
  assumes "a \<in> verts G"
  assumes "(a, hd p) \<in> arcs_ends G"
  shows "vwalk (a # p) G"
using assms by (cases p) (auto simp add: vwalk_def)

lemma vwalk_consE:
  assumes "vwalk (a # p) G"
  assumes "p \<noteq> []"
  assumes "(a, hd p) \<in> arcs_ends G \<Longrightarrow> vwalk p G \<Longrightarrow> P"
  shows "P"
using assms by (cases p) (auto simp add: vwalk_def)

lemma vwalk_induct[case_names Base Cons, induct pred: vwalk]:
  assumes "vwalk p G"
  assumes "\<And>u. u \<in> verts G \<Longrightarrow> P [u]"
  assumes "\<And>u v es. (u,v) \<in> arcs_ends G \<Longrightarrow> P (v # es) \<Longrightarrow> P (u # v # es)"
  shows "P p"
  using assms
proof (induct p)
  case (Cons u es)
  then show ?case
  proof (cases es)
    fix v es' assume "es = v # es'"
    then have "(u,v) \<in> arcs_ends G" and "P (v # es')"
      using Cons by (auto elim: vwalk_consE)
    then show ?thesis using \<open>es = v # es'\<close> Cons.prems by auto
  qed auto
qed auto

lemma vwalk_arcs_Cons[simp]:
  assumes "p \<noteq> []"
  shows "vwalk_arcs (u # p) = (u, hd p) # vwalk_arcs p"
using assms by (cases p) simp+

lemma vwalk_arcs_append:
  assumes "p \<noteq> []" and "q \<noteq> []"
  shows "vwalk_arcs (p @ q) = vwalk_arcs p @ (last p, hd q) # vwalk_arcs q" 
proof -
  from assms obtain a b p' q' where "p = a # p'" and "q = b # q'"
    by (auto simp add: neq_Nil_conv)
  moreover
  have "vwalk_arcs ((a # p') @ (b # q'))
    = vwalk_arcs (a # p') @ (last (a # p'), b) # vwalk_arcs (b # q')" 
  proof (induct p')
    case Nil show ?case by simp
  next
    case (Cons a' p') then show ?case by (auto simp add: neq_Nil_conv)
  qed
  ultimately
  show ?thesis by auto
qed

lemma set_vwalk_arcs_append1:
  "set (vwalk_arcs p) \<subseteq> set (vwalk_arcs (p @ q))" 
proof (cases p)
  case (Cons a p') note p_Cons = Cons then show ?thesis
  proof (cases q)
    case (Cons b q')
    with p_Cons  have "p \<noteq> []" and "q \<noteq> []" by auto
    then show ?thesis  by (auto simp add: vwalk_arcs_append)
  qed simp
qed simp

lemma set_vwalk_arcs_append2:
  "set (vwalk_arcs q) \<subseteq> set (vwalk_arcs (p @ q))" 
proof (cases p)
  case (Cons a p') note p_Cons = Cons then show ?thesis
  proof (cases q)
    case (Cons b q')
    with p_Cons have "p \<noteq> []" and "q \<noteq> []" by auto
    then show ?thesis by (auto simp add: vwalk_arcs_append)
  qed simp
qed simp

lemma set_vwalk_arcs_cons:
  "set (vwalk_arcs p) \<subseteq> set (vwalk_arcs (u # p))"
  by (cases p) auto

lemma set_vwalk_arcs_snoc:
  assumes "p \<noteq> []"
  shows "set (vwalk_arcs (p @ [a]))
    = insert (last p, a) (set (vwalk_arcs p))"
using assms proof (induct p)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof (cases "xs = []")
    case True then show ?thesis by auto
  next
    case False
    have "set (vwalk_arcs ((x # xs) @ [a]))
      = set (vwalk_arcs (x # (xs @ [a])))"
      by auto
    then show ?thesis using Cons and False
      by (auto simp add: set_vwalk_arcs_cons)
  qed
qed

lemma (in wf_digraph) vwalk_wf_digraph_consI:
  assumes "vwalk p G"
  assumes "(a, hd p) \<in> arcs_ends G"
  shows "vwalk (a # p) G"
proof
  show "a # p \<noteq> []" by simp

  from assms have "a \<in> verts G" and "set p \<subseteq> verts G" by auto
  then show "set (a # p) \<subseteq> verts G" by auto

  from \<open>vwalk p G\<close> have "p \<noteq> []" by auto
  then show "set (vwalk_arcs (a # p)) \<subseteq> arcs_ends G"
    using \<open>vwalk p G\<close> and \<open>(a, hd p) \<in> arcs_ends G\<close>
    by (auto simp add: set_vwalk_arcs_cons)
qed

lemma vwalkI_append_l:
  assumes "p \<noteq> []"
  assumes "vwalk (p @ q) G"
  shows "vwalk p G"
proof
  from assms show "p \<noteq> []" and "set p \<subseteq> verts G"
    by (auto elim!: vwalkE)
  have "set (vwalk_arcs p) \<subseteq> set (vwalk_arcs (p @ q))"
    by (auto simp add: set_vwalk_arcs_append1)
  then show "set (vwalk_arcs p) \<subseteq> arcs_ends G"
    using assms by blast
qed

lemma vwalkI_append_r:
  assumes "q \<noteq> []"
  assumes "vwalk (p @ q) G"
  shows "vwalk q G"
proof
  from \<open>vwalk (p @ q) G\<close> have "set (p @ q) \<subseteq> verts G" by blast
  then show "set q \<subseteq> verts G" by simp

  from \<open>vwalk (p @ q) G\<close> have "set (vwalk_arcs (p @ q)) \<subseteq> arcs_ends G"
    by blast
  then show "set (vwalk_arcs q) \<subseteq> arcs_ends G"
    by (metis set_vwalk_arcs_append2 subset_trans)

  from \<open>q \<noteq> []\<close> show "q \<noteq> []" by assumption
qed

lemma vwalk_to_vpath_hd: "hd (vwalk_to_vpath xs) = hd xs"
proof (induct xs rule: vwalk_to_vpath.induct)
  case (2 x xs) then show ?case
  proof (cases "x \<in> set xs")
    case True
    then have "hd (dropWhile (\<lambda>y. y \<noteq> x) xs) = x"
      using hd_dropWhile[where P="\<lambda>y. y \<noteq> x"] by auto
    then show ?thesis using True and 2 by auto
  qed auto
qed auto

lemma vwalk_to_vpath_induct3[consumes 0, case_names base in_set not_in_set]:
  assumes "P []"
  assumes "\<And>x xs. x \<in> set xs \<Longrightarrow> P (dropWhile (\<lambda>y. y \<noteq> x) xs)
    \<Longrightarrow> P (x # xs)"
  assumes "\<And>x xs. x \<notin> set xs \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)"
  shows "P xs"
using assms by (induct xs rule: vwalk_to_vpath.induct) auto

lemma vwalk_to_vpath_nonempty:
  assumes "p \<noteq> []"
  shows "vwalk_to_vpath p \<noteq> []"
using assms by (induct p rule: vwalk_to_vpath_induct3) auto

lemma vwalk_to_vpath_last:
  "last (vwalk_to_vpath xs) = last xs"
by (induct xs rule: vwalk_to_vpath_induct3)
   (auto simp add: dropWhile_last vwalk_to_vpath_nonempty)

lemma vwalk_to_vpath_subset:
  assumes "x \<in> set (vwalk_to_vpath xs)"
  shows "x \<in> set xs"
using assms proof (induct xs rule: vwalk_to_vpath.induct)
  case (2 x xs) then show ?case
    by (cases "x \<in> set xs") (auto dest: set_dropWhileD)
qed simp_all

lemma vwalk_to_vpath_cons:
  assumes "x \<notin> set xs"
  shows "vwalk_to_vpath (x # xs) = x # vwalk_to_vpath xs"
using assms by auto

lemma vwalk_to_vpath_vpath:
  assumes "vwalk p G"
  shows "vpath (vwalk_to_vpath p) G"
using assms proof (induct p rule: vwalk_to_vpath_induct3)
  case base then show ?case by auto
next
  case (in_set x xs)
  have set_neq: "\<And>x xs. x \<notin> set xs \<Longrightarrow> \<forall>x' \<in> set xs. x' \<noteq> x" by metis
  from \<open>x \<in> set xs\<close> obtain ys zs where "xs = ys @ x # zs" and "x \<notin> set ys"
    by (metis in_set_conv_decomp_first)
  then have vwalk_dW: "vwalk (dropWhile (\<lambda>y. y \<noteq> x) xs) G"
    using in_set and \<open>xs = ys @ x # zs\<close>
    by (auto simp add: dropWhile_append3 set_neq intro: vwalkI_append_r[where p="x # ys"])
  then show ?case using in_set
    by (auto simp add: vwalk_dW)
next
  case (not_in_set x xs)
  then have "x \<in> verts G" and x_notin: "x \<notin> set (vwalk_to_vpath xs)"
    by (auto intro: vwalk_to_vpath_subset)

  from not_in_set show ?case
  proof (cases "xs")
    case Nil then show ?thesis using not_in_set.prems by auto
  next
    case (Cons x' xs')
    have "vpath (vwalk_to_vpath xs) G"
      apply (rule not_in_set)
      apply (rule vwalkI_append_r[where p="[x]"])
       using Cons not_in_set by auto
    then have "vwalk (x # vwalk_to_vpath xs) G"
      apply (auto intro!: vwalk_consI simp add: vwalk_to_vpath_hd)
       using not_in_set
       apply -
       apply (erule vwalk_consE)
        using Cons
        apply (auto intro: \<open>x \<in> verts G\<close>)
      done
    then have "vpath (x # vwalk_to_vpath xs) G"
      apply (rule vpathI)
      using \<open>vpath (vwalk_to_vpath xs) G\<close>
      using x_notin
      by auto
    then show ?thesis using not_in_set
      by (auto simp add: vwalk_to_vpath_cons)
  qed
qed

lemma vwalk_imp_ex_vpath:
  assumes "vwalk p G"
  assumes "hd p = u"
  assumes "last p = v"
  shows "\<exists>q. vpath q G \<and> hd q = u \<and> last q = v"
by (metis assms vwalk_to_vpath_hd vwalk_to_vpath_last vwalk_to_vpath_vpath)


lemma vwalk_arcs_set_nil:
  assumes "x \<in> set (vwalk_arcs p)"
  shows "p \<noteq> []"
using assms by fastforce

lemma in_set_vwalk_arcs_append1:
  assumes "x \<in> set (vwalk_arcs p) \<or> x \<in> set (vwalk_arcs q)"
  shows "x \<in> set (vwalk_arcs (p @ q))"
using assms proof
  assume "x \<in> set (vwalk_arcs p)"
  then show "x \<in> set (vwalk_arcs (p @ q))"
    by (cases "q = []")
       (auto simp add: vwalk_arcs_append vwalk_arcs_set_nil)
next
  assume "x \<in> set (vwalk_arcs q)"
  then show "x \<in> set (vwalk_arcs (p @ q))"
    by (cases "p = []")
       (auto simp add: vwalk_arcs_append vwalk_arcs_set_nil)
qed

lemma in_set_vwalk_arcs_append2:
  assumes nonempty: "p \<noteq> []" "q \<noteq> []"
  assumes disj: "x \<in> set (vwalk_arcs p) \<or> x = (last p, hd q)
    \<or> x \<in> set (vwalk_arcs q)"
  shows "x \<in> set (vwalk_arcs (p @ q))"
using disj proof (elim disjE)
  assume "x = (last p, hd q)"
  then show "x \<in> set (vwalk_arcs (p @ q))"
    by (metis nonempty in_set_conv_decomp vwalk_arcs_append)
qed (auto intro: in_set_vwalk_arcs_append1)

lemma arcs_in_vwalk_arcs:
  assumes "u \<in> set (vwalk_arcs p)"
  shows "u \<in> set p \<times> set p"
using assms by (induct p rule: vwalk_arcs.induct) auto

lemma set_vwalk_arcs_rev:
  "set (vwalk_arcs (rev p)) = {(v, u). (u,v) \<in> set (vwalk_arcs p)}"
proof (induct p)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof (cases "xs = []")
    case True then show ?thesis by auto
  next
    case False
    then have "set (vwalk_arcs (rev (x # xs))) = {(hd xs, x)}
      \<union> {a. case a of (v, u) \<Rightarrow> (u, v) \<in> set (vwalk_arcs xs)}"
      by (simp add: set_vwalk_arcs_snoc last_rev Cons)
    also have "\<dots> = {a. case a of (v, u) \<Rightarrow> (u, v) \<in> set (vwalk_arcs (x # xs))}"
      using False by (auto simp add: set_vwalk_arcs_cons)
    finally show ?thesis by assumption
  qed
qed

lemma vpath_self:
  assumes "u \<in> verts G"
  shows "vpath [u] G"
using assms by (intro vpathI vwalkI, auto)

lemma vwalk_verts_in_verts:
  assumes "vwalk p G"
  assumes "u \<in> set p"
  shows "u \<in> verts G"
using assms by auto

lemma vwalk_arcs_tl:
  "vwalk_arcs (tl xs) = tl (vwalk_arcs xs)"
by (induct xs rule: vwalk_arcs.induct) simp_all

lemma vwalk_arcs_butlast:
  "vwalk_arcs (butlast xs) = butlast (vwalk_arcs xs)"
proof (induct xs rule: rev_induct)
  case (snoc x xs) thus ?case
  proof (cases "xs = []")
    case True with snoc show ?thesis by simp
  next
    case False
    hence "vwalk_arcs (xs @ [x]) = vwalk_arcs xs @ [(last xs, x)]" using vwalk_arcs_append by force
    with snoc show ?thesis by simp
  qed
qed simp

lemma vwalk_arcs_tl_empty:
  "vwalk_arcs xs = [] \<Longrightarrow> vwalk_arcs (tl xs) = []"
by (induct xs rule: vwalk_arcs.induct) simp_all

lemma vwalk_arcs_butlast_empty:
  "xs \<noteq> [] \<Longrightarrow> vwalk_arcs xs = [] \<Longrightarrow> vwalk_arcs (butlast xs) = []"
by (induct xs rule: vwalk_arcs.induct) simp_all


definition joinable :: "'a vwalk \<Rightarrow> 'a vwalk \<Rightarrow> bool" where
  "joinable p q \<equiv> last p = hd q \<and> p \<noteq> [] \<and> q \<noteq> []"

definition vwalk_join :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  (infixr "\<oplus>" 65) where
  "p \<oplus> q \<equiv> p @ tl q"

lemma joinable_Nil_l_iff[simp]: "joinable [] p = False"
  and joinable_Nil_r_iff[simp]: "joinable q [] = False"
  by (auto simp: joinable_def)

lemma joinable_Cons_l_iff[simp]: "p \<noteq> [] \<Longrightarrow> joinable (v # p) q = joinable p q"
  and joinable_Snoc_r_iff[simp]: "q \<noteq> [] \<Longrightarrow> joinable p (q @ [v]) = joinable p q"
   by (auto simp: joinable_def)

lemma joinableI[intro,simp]:
  assumes "last p = hd q" "p \<noteq> []" "q \<noteq> []"
  shows "joinable p q"
using assms by (simp add: joinable_def)

lemma vwalk_join_non_Nil[simp]:
  assumes "p \<noteq> []"
  shows "p \<oplus> q \<noteq> []"
unfolding vwalk_join_def using assms by simp

lemma vwalk_join_Cons[simp]:
  assumes "p \<noteq> []"
  shows "(u # p) \<oplus> q = u # p \<oplus> q"
unfolding vwalk_join_def using assms by simp

lemma vwalk_join_def2:
  assumes "joinable p q"
  shows "p \<oplus> q = butlast p @ q"
proof -
  from assms have "p \<noteq> []" and "q \<noteq> []" by (simp add: joinable_def)+
  then have "vwalk_join p q = butlast p @ last p # tl q"
    unfolding vwalk_join_def by simp
  then show ?thesis using assms by (simp add: joinable_def)
qed

lemma vwalk_join_hd':
  assumes "p \<noteq> []"
  shows "hd (p \<oplus> q) = hd p"
using assms by (auto simp add: vwalk_join_def)

lemma vwalk_join_hd:
  assumes "joinable p q"
  shows "hd (p \<oplus> q) = hd p"
using assms by (auto simp add: vwalk_join_def joinable_def)

lemma vwalk_join_last:
  assumes "joinable p q"
  shows "last (p \<oplus> q) = last q"
using assms by (auto simp add: vwalk_join_def2 joinable_def)

lemma vwalk_join_Nil[simp]:
  "p \<oplus> [] = p"
by (simp add: vwalk_join_def)

lemma vwalk_joinI_vwalk':
  assumes "vwalk p G"
  assumes "vwalk q G"
  assumes "last p = hd q"
  shows "vwalk (p \<oplus> q) G"
proof (unfold vwalk_join_def, rule vwalkI)
  have "set p \<subseteq> verts G" and "set q \<subseteq> verts G"
    using \<open>vwalk p G\<close> and \<open>vwalk q G\<close> by blast+
  then show "set (p @ tl q) \<subseteq> verts G"
    by (cases q) auto
next
  show "p @ tl q \<noteq> []" using \<open>vwalk p G\<close> by auto
next
  have pe_p: "set (vwalk_arcs p) \<subseteq> arcs_ends G"
    using \<open>vwalk p G\<close> by blast
  have pe_q': "set (vwalk_arcs (tl q)) \<subseteq> arcs_ends G"
  proof -
    have "set (vwalk_arcs (tl q)) \<subseteq> set (vwalk_arcs q)"
      by (cases q) (simp_all add: set_vwalk_arcs_cons)
    then show ?thesis using \<open>vwalk q G\<close> by blast
  qed

  show "set (vwalk_arcs (p @ tl q)) \<subseteq> arcs_ends G"
  proof (cases "tl q")
    case Nil then show ?thesis using pe_p by auto
  next
    case (Cons x xs)
    then have nonempty: "p \<noteq> []" "tl q \<noteq> []"
      using \<open>vwalk p G\<close> by auto
    moreover
    have "(hd q, hd (tl q)) \<in> set (vwalk_arcs q)"
      using \<open>vwalk q G\<close> Cons by  (cases q) auto
    ultimately show ?thesis
      using \<open>vwalk q G\<close>
      by (auto simp: pe_p pe_q' \<open>last p = hd q\<close> vwalk_arcs_append)
  qed
qed

lemma vwalk_joinI_vwalk:
  assumes "vwalk p G"
  assumes "vwalk q G"
  assumes "joinable p q"
  shows "vwalk (p \<oplus> q) G"
using assms vwalk_joinI_vwalk' by (auto simp: joinable_def)

lemma vwalk_join_split:
  assumes "u \<in> set p"
  shows "\<exists>q r. p = q \<oplus> r
  \<and> last q = u \<and> hd r = u \<and> q \<noteq> [] \<and> r \<noteq> []"
proof -
  from \<open>u \<in> set p\<close>
  obtain pre_p post_p where "p = pre_p @ u # post_p"
    by atomize_elim (auto simp add: split_list)
  then have "p = (pre_p @ [u]) \<oplus> (u # post_p)"
    unfolding vwalk_join_def by simp
  then show ?thesis by fastforce
qed

lemma vwalkI_vwalk_join_l:
  assumes "p \<noteq> []"
  assumes "vwalk (p \<oplus> q) G"
  shows "vwalk p G"
using assms unfolding vwalk_join_def
by (auto intro: vwalkI_append_l)

lemma vwalkI_vwalk_join_r:
  assumes "joinable p q"
  assumes "vwalk (p \<oplus> q) G"
  shows "vwalk q G"
using assms
by (auto simp add: vwalk_join_def2 joinable_def intro: vwalkI_append_r)

lemma vwalk_join_assoc':
  assumes "p \<noteq> []" "q \<noteq> []"
  shows "(p \<oplus> q) \<oplus> r = p \<oplus> q \<oplus> r"
using assms by (simp add: vwalk_join_def)

lemma vwalk_join_assoc:
  assumes "joinable p q" "joinable q r"
  shows "(p \<oplus> q) \<oplus> r = p \<oplus> q \<oplus> r"
using assms by (simp add: vwalk_join_def joinable_def)

lemma joinable_vwalk_join_r_iff:
  "joinable p (q \<oplus> r) \<longleftrightarrow> joinable p q \<or> (q = [] \<and> joinable p (tl r))"
by (cases q) (auto simp add: vwalk_join_def joinable_def)

lemma joinable_vwalk_join_l_iff:
  assumes "joinable p q"
  shows "joinable (p \<oplus> q) r \<longleftrightarrow> joinable q r" (is "?L \<longleftrightarrow> ?R")
  using assms by (auto simp: joinable_def vwalk_join_last)

lemmas joinable_simps =
  joinable_vwalk_join_l_iff
  joinable_vwalk_join_r_iff

lemma joinable_cyclic_omit:
  assumes "joinable p q" "joinable q r" "joinable q q"
  shows "joinable p r"
using assms by (metis joinable_def)

lemma joinable_non_Nil:
  assumes "joinable p q"
  shows "p \<noteq> []" "q \<noteq> []"
using assms by (simp_all add: joinable_def)

lemma vwalk_join_vwalk_length[simp]:
  assumes "joinable p q"
  shows "vwalk_length (p \<oplus> q) = vwalk_length p + vwalk_length q"
using assms unfolding vwalk_join_def
by (simp add: less_eq_Suc_le[symmetric] joinable_non_Nil)

lemma vwalk_join_arcs:
  assumes "joinable p q"
  shows "vwalk_arcs (p \<oplus> q) = vwalk_arcs p @ vwalk_arcs q"
  using assms
proof (induct p)
  case (Cons v vs) then show ?case 
    by (cases "vs = []")
       (auto simp: vwalk_join_hd, simp add: joinable_def vwalk_join_def)
qed simp

lemma vwalk_join_arcs1:
  assumes "set (vwalk_arcs p) \<subseteq> E"
  assumes "p = q \<oplus> r"
  shows "set (vwalk_arcs q) \<subseteq> E"
by (metis assms vwalk_join_def set_vwalk_arcs_append1 subset_trans)

lemma vwalk_join_arcs2:
  assumes "set (vwalk_arcs p) \<subseteq> E"
  assumes "joinable q r"
  assumes "p = q \<oplus> r"
  shows "set (vwalk_arcs r) \<subseteq> E"
using assms by (simp add: vwalk_join_arcs)


definition concat_vpath :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "concat_vpath p q \<equiv> vwalk_to_vpath (p \<oplus> q)"

lemma concat_vpath_is_vpath:
  assumes p_props: "vwalk p G" "hd p = u" "last p = v"
  assumes q_props: "vwalk q G" "hd q = v" "last q = w"
  shows "vpath (concat_vpath p q) G \<and> hd (concat_vpath p q) = u
    \<and> last (concat_vpath p q) = w"
proof (intro conjI)
  have joinable: "joinable p q" using assms by auto

  show "vpath (concat_vpath p q) G"
    unfolding concat_vpath_def using assms and joinable
    by (auto intro: vwalk_to_vpath_vpath vwalk_joinI_vwalk)

  show "hd (concat_vpath p q) = u" "last (concat_vpath p q) = w"
    unfolding concat_vpath_def using assms and joinable
    by (auto simp: vwalk_to_vpath_hd vwalk_to_vpath_last
      vwalk_join_hd vwalk_join_last)
qed

lemma concat_vpath_exists:
  assumes p_props: "vwalk p G" "hd p = u" "last p = v"
  assumes q_props: "vwalk q G" "hd q = v" "last q = w"
  obtains r where "vpath r G" "hd r = u" "last r = w"
using concat_vpath_is_vpath[OF assms] by blast

lemma (in fin_digraph) vpaths_finite:
  shows "finite {p. vpath p G}"
proof -
  have "{p. vpath p G}
    \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs \<le> card (verts G)}"
  proof (clarify, rule conjI)
    fix p assume "vpath p G"
    then show "set p \<subseteq> verts G" by blast

    from \<open>vpath p G\<close> have "length p = card (set p)"
      by (auto simp add: distinct_card)
    also have "\<dots> \<le> card (verts G)"
      using \<open>vpath p G\<close>
      by (auto intro!: card_mono elim!: vpathE)
    finally show "length p \<le> card (verts G)" .
  qed
  moreover
  have "finite {xs. set xs \<subseteq> verts G \<and> length xs \<le> card (verts G)}"
    by (intro finite_lists_length_le) auto
  ultimately show ?thesis by (rule finite_subset)
qed

lemma (in wf_digraph) reachable_vwalk_conv:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> (\<exists>p. vwalk p G \<and> hd p = u \<and> last p = v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
  proof (induct rule: converse_reachable_induct)
    case base then show ?case
      by (rule_tac x="[v]" in exI)
         (auto simp: vwalk_def arcs_ends_conv)
  next
    case (step u w)
    then obtain p where "vwalk p G" "hd p = w" "last p = v" by auto
    then have "vwalk (u#p) G \<and> hd (u#p) = u \<and> last (u#p) = v"
      using step by (auto intro!: vwalk_consI intro: adj_in_verts)
    then show ?case ..
  qed
next
  assume ?R
  then obtain p where "vwalk p G" "hd p = u" "last p = v" by auto
  with \<open>vwalk p G\<close> show ?L
  proof (induct p arbitrary: u rule: vwalk_induct)
    case (Base u) then show ?case by auto
  next
    case (Cons w x es)
    then have "u \<rightarrow>\<^bsub>G\<^esub> x" using Cons by auto
    show ?case
      apply (rule adj_reachable_trans)
      apply fact
      apply (rule Cons)
      using Cons by (auto elim: vwalk_consE)
  qed
qed

lemma (in wf_digraph) reachable_vpath_conv:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> (\<exists>p. vpath p G \<and> hd p = u \<and> last p = v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then obtain p where "vwalk p G" "hd p = u" "last p = v"
    by (auto simp: reachable_vwalk_conv)
  then show ?R
    by (auto intro: exI[where x="vwalk_to_vpath p"]
      simp: vwalk_to_vpath_hd vwalk_to_vpath_last vwalk_to_vpath_vpath)
qed (auto simp: reachable_vwalk_conv)

lemma in_set_vwalk_arcsE:
  assumes "(u,v) \<in> set (vwalk_arcs p)"
  obtains "u \<in> set p" "v \<in> set p"
using assms
by (induct p rule: vwalk_arcs.induct) auto

lemma vwalk_rev_ex:
  assumes "symmetric G"
  assumes "vwalk p G"
  shows "vwalk (rev p) G"
using assms
proof (induct p)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then show ?case proof (cases "xs = []")
    case True then show ?thesis using Cons by auto
  next
    case False
    then have "vwalk xs G" using \<open>vwalk (x # xs) G\<close>
      by (metis vwalk_consE)
    then have "vwalk (rev xs) G" using Cons by blast
    have "vwalk (rev (x # xs)) G"
    proof (rule vwalkI)
      have "set (x # xs) \<subseteq> verts G" using \<open>vwalk (x # xs) G\<close> by blast
      then show "set (rev (x # xs)) \<subseteq> verts G" by auto
    next
      have "set (vwalk_arcs (x # xs)) \<subseteq> arcs_ends G"
        using \<open>vwalk (x # xs) G\<close> by auto
      then show "set (vwalk_arcs (rev (x # xs))) \<subseteq> arcs_ends G"
        using \<open>symmetric G\<close>
        by (simp only: set_vwalk_arcs_rev)
           (auto intro: arcs_ends_symmetric)
    next
      show "rev (x # xs) \<noteq> []" by auto
    qed
    then show "vwalk (rev (x # xs)) G" by auto
  qed
qed

lemma vwalk_singleton[simp]: "vwalk [u] G = (u \<in> verts G)"
  by auto

lemma (in wf_digraph) vwalk_Cons_Cons[simp]:
  "vwalk (u # v # ws) G = ((u,v) \<in> arcs_ends G \<and> vwalk (v # ws) G)"
  by (force elim: vwalk_consE intro: vwalk_consI)

lemma (in wf_digraph) awalk_imp_vwalk:
  assumes "awalk u p v" shows "vwalk (awalk_verts u p) G"
  using assms
  by (induct p arbitrary: u rule: vwalk_arcs.induct)
     (force simp: awalk_simps dest: in_arcs_imp_in_arcs_ends)+

end
