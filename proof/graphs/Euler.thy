(* Title:  Euler.thy
   Author: Lars Noschinski, TU München
*)
theory Euler imports
  Arc_Walk
  Digraph_Component
  Digraph_Isomorphism
begin

section \<open>Euler Trails in Digraphs\<close>

text \<open>
  In this section we prove the well-known theorem characterizing the
  existence of an Euler Trail in an directed graph
\<close>

subsection \<open>Trails and Euler Trails\<close>

definition (in pre_digraph) euler_trail :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "euler_trail u p v \<equiv> trail u p v \<and> set p = arcs G \<and> set (awalk_verts u p) = verts G"

context wf_digraph begin

(* XXX move; notused*)
lemma finite_distinct:
  assumes "finite A" shows "finite {p. distinct p \<and> set p \<subseteq> A}"
proof -
  have "{p. distinct p \<and> set p \<subseteq> A} \<subseteq> {p. set p \<subseteq> A \<and> length p \<le> card A}"
    using assms by (auto simp: distinct_card[symmetric] intro: card_mono)
  also have "finite ..."
    using assms by (simp add: finite_lists_length_le)
  finally (finite_subset) show ?thesis .
qed

(* XXX move; notused*)
lemma (in fin_digraph) trails_finite: "finite {p. \<exists>u v. trail u p v}"
proof -
  have "{p. \<exists>u v. trail u p v} \<subseteq> {p. distinct p \<and> set p \<subseteq> arcs G}"
    by (auto simp: trail_def)
  with finite_arcs finite_distinct show ?thesis by (blast intro: finite_subset)
qed
(* XXX: simplify apath_finite proof? *)

lemma rotate_awalkE:
  assumes "awalk u p u" "w \<in> set (awalk_verts u p)"
  obtains q r where "p = q @ r" "awalk w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
proof -
  from assms obtain q r where A: "p = q @ r" and A': "awalk u q w" "awalk w r u"
    by atomize_elim (rule awalk_decomp)
  
  then have B: "awalk w (r @ q) w" by auto

  have C: "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
    using \<open>awalk u p u\<close> A A' by (auto simp: set_awalk_verts_append)

  from A B C show ?thesis ..
qed

lemma rotate_trailE:
  assumes "trail u p u" "w \<in> set (awalk_verts u p)"
  obtains q r where "p = q @ r" "trail w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
  using assms by - (rule rotate_awalkE[where u=u and p=p and w=w], auto simp: trail_def)

lemma rotate_trailE':
  assumes "trail u p u" "w \<in> set (awalk_verts u p)"
  obtains q where "trail w q w" "set q = set p" "set (awalk_verts w q) = set (awalk_verts u p)"
proof -
  from assms obtain q r where "p = q @ r" "trail w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
    by (rule rotate_trailE)
  then have "set (r @ q) = set p" by auto
  show ?thesis by (rule that) fact+
qed

lemma sym_reachableI_in_awalk:
  assumes walk: "awalk u p v" and
    w1: "w1 \<in> set (awalk_verts u p)" and w2: "w2 \<in> set (awalk_verts u p)"
  shows "w1 \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> w2"
proof -
  from walk w1 obtain q r where "p = q @ r" "awalk u q w1" "awalk w1 r v"
    by (atomize_elim) (rule awalk_decomp)
  then have w2_in: "w2 \<in> set (awalk_verts u q) \<union> set (awalk_verts w1 r)"
    using w2 by (auto simp: set_awalk_verts_append)

  show ?thesis
  proof cases
    assume A: "w2 \<in> set (awalk_verts u q)"
    obtain s where "awalk w2 s w1"
      using awalk_decomp[OF \<open>awalk u q w1\<close> A] by blast
    then have "w2 \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> w1" 
      by (intro reachable_awalkI reachable_mk_symmetricI)
    with symmetric_mk_symmetric show ?thesis by (rule symmetric_reachable)
  next
    assume "w2 \<notin> set (awalk_verts u q)"
    then have A: "w2 \<in> set (awalk_verts w1 r)"
      using w2_in by blast
    obtain s where "awalk w1 s w2"
      using awalk_decomp[OF \<open>awalk w1 r v\<close> A] by blast
    then show "w1 \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> w2" 
      by (intro reachable_awalkI reachable_mk_symmetricI)
  qed
qed

lemma euler_imp_connected:
  assumes "euler_trail u p v" shows "connected G"
proof -
  { have "verts G \<noteq> {}" using assms unfolding euler_trail_def trail_def by auto }
  moreover
  { fix w1 w2 assume "w1 \<in> verts G" "w2 \<in> verts G"
    then have "awalk u p v " "w1 \<in> set (awalk_verts u p)" "w2 \<in> set (awalk_verts u p)"
      using assms by (auto simp: euler_trail_def trail_def)
    then have "w1 \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> w2" by (rule sym_reachableI_in_awalk) }
  ultimately show "connected G" by (rule connectedI)
qed

end



subsection \<open>Arc Balance of Walks\<close>

context pre_digraph begin

(* XXX change order of arguments? *)
definition arc_set_balance :: "'a \<Rightarrow> 'b set \<Rightarrow> int" where
  "arc_set_balance w A = int (card (in_arcs G w \<inter> A)) - int (card (out_arcs G w \<inter> A))"

definition  arc_set_balanced :: "'a \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> bool" where
  "arc_set_balanced u A v \<equiv>
      if u = v then (\<forall>w \<in> verts G. arc_set_balance w A = 0)
      else (\<forall>w \<in> verts G. (w \<noteq> u \<and> w \<noteq> v) \<longrightarrow> arc_set_balance w A = 0)
        \<and> arc_set_balance u A = -1
        \<and> arc_set_balance v A = 1"

abbreviation arc_balance :: "'a \<Rightarrow> 'b awalk \<Rightarrow> int" where
  "arc_balance w p \<equiv> arc_set_balance w (set p)"

abbreviation arc_balanced :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "arc_balanced u p v \<equiv> arc_set_balanced u (set p) v"

lemma arc_set_balanced_all:
  "arc_set_balanced u (arcs G) v =
      (if u = v then (\<forall>w \<in> verts G. in_degree G w = out_degree G w)
      else (\<forall>w \<in> verts G. (w \<noteq> u \<and> w \<noteq> v) \<longrightarrow> in_degree G w = out_degree G w)
        \<and> in_degree G u + 1 = out_degree G u
        \<and> out_degree G v + 1 = in_degree G v)"
  unfolding arc_set_balanced_def arc_set_balance_def in_degree_def out_degree_def by auto

end

context wf_digraph begin


(* XXX tune assumption? e \<notin> set es oder so? *)
lemma arc_balance_Cons:
  assumes "trail u (e # es) v"
  shows "arc_set_balance w (insert e (set es)) = arc_set_balance w {e} + arc_balance w es"
proof -
  from assms have "e \<notin> set es" "e \<in> arcs G" by (auto simp: trail_def)

  with \<open>e \<notin> set es\<close> show ?thesis
    apply (cases "w = tail G e")
     apply (case_tac [!] "w = head G e")
       apply (auto simp: arc_set_balance_def)
    done
qed

lemma arc_balancedI_trail:
  assumes "trail u p v" shows "arc_balanced u p v"
  using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by (auto simp: arc_set_balanced_def arc_set_balance_def trail_def)
next
  case (Cons e es)
  then have "arc_balanced (head G e) es v" "u = tail G e" "e \<in> arcs G"
    by (auto simp: awalk_Cons_iff trail_def)
  moreover
  have "\<And>w. arc_balance w [e] = (if w = tail G e \<and> tail G e \<noteq> head G e then -1
      else if w = head G e \<and> tail G e \<noteq> head G e then 1 else 0)"
      using \<open>e \<in> _\<close> by (case_tac "w = tail G e") (auto simp: arc_set_balance_def)
  ultimately show ?case
    by (auto simp: arc_set_balanced_def arc_balance_Cons[OF \<open>trail u _ _\<close>])
qed

lemma trail_arc_balanceE:
  assumes "trail u p v"
  obtains "\<And>w. \<lbrakk> u = v \<or> (w \<noteq> u \<and> w \<noteq> v); w \<in> verts G \<rbrakk>
      \<Longrightarrow> arc_balance w p = 0"
    and "\<lbrakk> u \<noteq> v \<rbrakk> \<Longrightarrow> arc_balance u p = - 1"
    and "\<lbrakk> u \<noteq> v \<rbrakk> \<Longrightarrow> arc_balance v p = 1"
  using arc_balancedI_trail[OF assms] unfolding arc_set_balanced_def by (intro that) (metis,presburger+)

end



subsection \<open>Closed Euler Trails\<close>

lemma (in wf_digraph) awalk_vertex_props:
  assumes "awalk u p v" "p \<noteq> []"
  assumes "\<And>w. w \<in> set (awalk_verts u p) \<Longrightarrow> P w \<or> Q w"
  assumes "P u" "Q v"
  shows "\<exists>e \<in> set p. P (tail G e) \<and> Q (head G e)"
  using assms(2,1,3-)
proof (induct p arbitrary: u rule: list_nonempty_induct)
  case (cons e es)
  show ?case
  proof (cases "P (tail G e) \<and> Q (head G e)")
    case False
    then have "P (head G e) \<or> Q (head G e)"
      using cons.prems(1) cons.prems(2)[of "head G e"]
      by (auto simp: awalk_Cons_iff set_awalk_verts)
    then have "P (tail G e) \<and> P (head G e)"
      using False using cons.prems(1,3) by auto
    
    then have "\<exists>e \<in> set es. P (tail G e) \<and> Q (head G e)"
      using cons by (auto intro: cons simp: awalk_Cons_iff)
    then show ?thesis by auto
  qed auto
qed (simp add: awalk_simps)

lemma (in wf_digraph) connected_verts:
  assumes "connected G" "arcs G \<noteq> {}"
  shows "verts G = tail G ` arcs G \<union> head G ` arcs G"
proof -
  { assume "verts G = {}" then have ?thesis by (auto dest: tail_in_verts) }
  moreover
  { assume "\<exists>v. verts G = {v}"
    then obtain v where "verts G = {v}" by (auto simp: card_Suc_eq)
    moreover
    with \<open>arcs G \<noteq> {}\<close> obtain e where "e \<in> arcs G" "tail G e = v" "head G e = v"
      by (auto dest: tail_in_verts head_in_verts)
    moreover have "tail G ` arcs G \<union> head G ` arcs G \<subseteq> verts G" by auto 
    ultimately have ?thesis by auto }
  moreover
  { assume A: "\<exists>u v. u \<in> verts G \<and> v \<in> verts G \<and> u \<noteq> v"
    { fix u assume "u \<in> verts G"

      interpret S: pair_wf_digraph "mk_symmetric G" by rule
      from A obtain v where "v \<in> verts G" "u \<noteq> v" by blast
      then obtain p where "S.awalk u p v"
        using \<open>connected G\<close> \<open>u \<in> verts G\<close> by (auto elim: connected_awalkE)
      with \<open>u \<noteq> v\<close> obtain e where "e \<in> parcs (mk_symmetric G)" "fst e = u"
        by (metis S.awalk_Cons_iff S.awalk_empty_ends list_exhaust2)
      then obtain e' where "tail G e' = u \<or> head G e' = u" "e' \<in> arcs G"
        by (force simp: parcs_mk_symmetric)
      then have "u \<in> tail G ` arcs G \<union> head G `arcs G" by auto }
    then have ?thesis by auto }
  ultimately show ?thesis by blast
qed

lemma (in wf_digraph) connected_arcs_empty:
  assumes "connected G" "arcs G = {}" "verts G \<noteq> {}" obtains v where "verts G = {v}"
proof (atomize_elim, rule ccontr)
  assume A: "\<not> (\<exists>v. verts G = {v})"

  interpret S: pair_wf_digraph "mk_symmetric G" by rule

  from \<open>verts G \<noteq> {}\<close> obtain u where "u \<in> verts G" by auto
  with A obtain v where "v \<in> verts G" "u \<noteq> v" by auto

  from \<open>connected G\<close> \<open>u \<in> verts G\<close> \<open>v \<in> verts G\<close>
  obtain p where "S.awalk u p v"
    using \<open>connected G\<close> \<open>u \<in> verts G\<close> by (auto elim: connected_awalkE)
  with \<open>u \<noteq> v\<close> obtain e where "e \<in> parcs (mk_symmetric G)"
    by (metis S.awalk_Cons_iff S.awalk_empty_ends list_exhaust2)
  with \<open>arcs G = {}\<close> show False
    by (auto simp: parcs_mk_symmetric)
qed

lemma (in wf_digraph) euler_trail_conv_connected:
  assumes "connected G"
  shows "euler_trail u p v \<longleftrightarrow> trail u p v \<and> set p = arcs G" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?R show ?L
  proof cases
    assume "p = []" with assms \<open>?R\<close> show ?thesis
      by (auto simp: euler_trail_def trail_def awalk_def elim: connected_arcs_empty)
  next
    assume "p \<noteq> []" then have "arcs G \<noteq> {}" using \<open>?R\<close> by auto
    with assms \<open>?R\<close> \<open>p \<noteq> []\<close> show ?thesis
      by (auto simp: euler_trail_def trail_def set_awalk_verts_not_Nil connected_verts)
  qed
qed (simp add: euler_trail_def)

lemma (in wf_digraph) awalk_connected:
  assumes "connected G" "awalk u p v" "set p \<noteq> arcs G"
  shows "\<exists>e. e \<in> arcs G - set p \<and> (tail G e \<in> set (awalk_verts u p) \<or> head G e \<in> set (awalk_verts u p))"
proof (rule ccontr)
  assume A: "\<not>?thesis"

  obtain e where "e \<in> arcs G - set p"
    using assms by (auto simp: trail_def)
  with A have "tail G e \<notin> set (awalk_verts u p)" "tail G e \<in> verts G"
    by auto

  interpret S: pair_wf_digraph "mk_symmetric G" ..

  have "u \<in> verts G" using \<open>awalk u p v\<close> by (auto simp: awalk_hd_in_verts)
  with \<open>tail G e \<in> _\<close> and \<open>connected G\<close>
  obtain q where q: "S.awalk u q (tail G e)"
    by (auto elim: connected_awalkE)

  have "u \<in> set (awalk_verts u p)"
    using \<open>awalk u p v\<close> by (auto simp: set_awalk_verts)

  have "q \<noteq> []" using \<open>u \<in> set _\<close> \<open>tail G e \<notin> _\<close> q by auto

  have "\<exists>e \<in> set q. fst e \<in> set (awalk_verts u p) \<and> snd e \<notin> set (awalk_verts u p)"
    by (rule S.awalk_vertex_props[OF \<open>S.awalk _ _ _\<close> \<open>q \<noteq> []\<close>]) (auto simp: \<open>u \<in> set _\<close> \<open>tail G e \<notin> _\<close>)
  then obtain se' where se': "se' \<in> set q" "fst se' \<in> set (awalk_verts u p)" "snd se' \<notin> set (awalk_verts u p)"
    by auto

  from se' have "se' \<in> parcs (mk_symmetric G)" using q by auto
  then obtain e' where "e' \<in> arcs G" "(tail G e' = fst se' \<and> head G e' = snd se') \<or> (tail G e' = snd se' \<and> head G e' = fst se')"
    by (auto simp: parcs_mk_symmetric)
  moreover
  then have "e' \<notin> set p" using se' \<open>awalk u p v\<close>
    by (auto dest: awalk_verts_arc2 awalk_verts_arc1)
  ultimately show False using se'
    using A by auto
qed

lemma (in wf_digraph) trail_connected:
  assumes "connected G" "trail u p v" "set p \<noteq> arcs G"
  shows "\<exists>e. e \<in> arcs G - set p \<and> (tail G e \<in> set (awalk_verts u p) \<or> head G e \<in> set (awalk_verts u p))"
  using assms by (intro awalk_connected) (auto simp: trail_def)

theorem (in fin_digraph) closed_euler1:
  assumes con: "connected G"
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u"
  shows "\<exists>u p. euler_trail u p u"
proof -
  from con obtain u where "u \<in> verts G" by (auto simp: connected_def strongly_connected_def)
  then have "trail u [] u" by (auto simp: trail_def awalk_simps)
  moreover
  { fix u p v assume  "trail u p v"
    then have "\<exists>u' p' v'. euler_trail u' p' v'"
    proof (induct "card (arcs G) - length p" arbitrary: u p v)
      case 0
      then have "u \<in> verts G" by (auto simp: trail_def)

      have "set p \<subseteq> arcs G" using \<open>trail u p v\<close> by (auto simp: trail_def)
      with 0 have "set p = arcs G"
        by (auto simp: trail_def distinct_card[symmetric] card_seteq)
      then have "euler_trail u p v"
        using 0 by (simp add: euler_trail_conv_connected[OF con])
      then show ?case by blast
    next
      case (Suc n)
      then have neq: "set p \<noteq> arcs G" "u \<in> verts G"
        by (auto simp: trail_def distinct_card[symmetric])

      show ?case
      proof (cases "u = v")
        assume "u \<noteq> v"
        then have "arc_balance u p = -1"
          using Suc neq by (auto elim: trail_arc_balanceE)
        then have "card (in_arcs G u \<inter> set p) < card (out_arcs G u \<inter> set p)"
          unfolding arc_set_balance_def by auto
        also have "\<dots> \<le> card (out_arcs G u)"
          by (rule card_mono) auto
        finally have "card (in_arcs G u \<inter> set p) < card (in_arcs G u)"
          using deg[OF \<open>u \<in> _\<close>] unfolding out_degree_def in_degree_def by simp
        then have "in_arcs G u - set p \<noteq> {}"
          by (auto dest: card_psubset[rotated 2])
        then obtain a where "a \<in> arcs G" "head G a = u" "a \<notin> set p"
          by (auto simp: in_arcs_def)
        then have *: "trail (tail G a) (a # p) v"
          using Suc by (auto simp: trail_def awalk_simps)
        then show ?thesis
          using Suc by (intro Suc) auto
      next
        assume "u = v"
        with neq con Suc
        obtain a where a_in: "a \<in> arcs G - set p"
            and a_end: "(tail G a \<in> set (awalk_verts u p) \<or> head G a \<in> set (awalk_verts u p))"
          by (atomize_elim) (rule trail_connected)
        have "trail u p u" using Suc \<open>u = v\<close> by simp
        show ?case
        proof (cases "tail G a \<in> set (awalk_verts u p)")
          case True
          with \<open>trail u p u\<close> obtain q where q: "set p = set q" "trail (tail G a) q (tail G a)"
            by (rule rotate_trailE') blast
          with True a_in have *: "trail (tail G a) (q @ [a]) (head G a)"
            by (fastforce simp: trail_def awalk_simps )
          moreover
          from q Suc have "length q = length p"
            by (simp add: trail_def distinct_card[symmetric])
          ultimately
          show ?thesis using Suc  by (intro Suc) auto
        next
          case False
          with a_end have "head G a \<in> set (awalk_verts u p)" by blast
          with \<open>trail u p u\<close> obtain q where q: "set p = set q" "trail (head G a) q (head G a)"
            by (rule rotate_trailE') blast
          with False a_in have *: "trail (tail G a) (a # q) (head G a)"
            by (fastforce simp: trail_def awalk_simps )
          moreover
          from q Suc have "length q = length p"
            by (simp add: trail_def distinct_card[symmetric])
          ultimately
          show ?thesis using Suc by (intro Suc) auto
        qed
      qed
    qed }
  ultimately obtain u p v where et: "euler_trail u p v" by blast
  moreover
  have "u = v"
  proof -
    have "arc_balanced u p v"
      using \<open>euler_trail u p v\<close> by (auto simp: euler_trail_def dest: arc_balancedI_trail)
    then show ?thesis
      using \<open>euler_trail u p v\<close> deg
      by (auto simp add: euler_trail_def trail_def arc_set_balanced_all split: if_split_asm)
  qed
  ultimately show ?thesis by blast
qed

lemma (in wf_digraph) closed_euler_imp_eq_degree:
  assumes "euler_trail u p u"
  assumes "v \<in> verts G"
  shows "in_degree G v = out_degree G v"
proof -
  from assms have "arc_balanced u p u" "set p = arcs G"
    unfolding euler_trail_def by (auto dest: arc_balancedI_trail)
  with assms have "arc_balance v p = 0"
    unfolding arc_set_balanced_def by auto
  moreover
  from \<open>set p = _\<close> have "in_arcs G v \<inter> set p = in_arcs G v" "out_arcs G v \<inter> set p = out_arcs G v"
    by (auto intro: in_arcs_in_arcs out_arcs_in_arcs)
  ultimately
  show ?thesis unfolding arc_set_balance_def in_degree_def out_degree_def by auto
qed



theorem (in fin_digraph) closed_euler2:
  assumes "euler_trail u p u"
  shows "connected G"
    and "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u" (is "\<And>u. _ \<Longrightarrow> ?eq_deg u")
proof -
  from assms show "connected G" by (rule euler_imp_connected)
next
  fix v assume A: "v \<in> verts G"
  with assms show "?eq_deg v" by (rule closed_euler_imp_eq_degree)
qed

corollary (in fin_digraph) closed_euler:
  "(\<exists>u p. euler_trail u p u) \<longleftrightarrow> connected G \<and> (\<forall>u \<in> verts G. in_degree G u = out_degree G u)"
  by (auto dest: closed_euler1 closed_euler2)



subsection \<open>Open euler trails\<close>

text \<open>
  Intuitively, a graph has an open euler trail if and only if it is possible to add
  an arc such that the resulting graph has a closed euler trail. However, this is
  not true in our formalization, as the arc type @{typ 'b} might be finite:

  Consider for example the graph
  @{term "\<lparr> verts = {0,1}, arcs = {()}, tail = \<lambda>_. 0, head = \<lambda>_. 1 \<rparr>"}. This graph
  obviously has an open euler trail, but we cannot add another arc, as we already
  exhausted the universe.

  However, for each @{term "fin_digraph G"} there exist an isomorphic graph
  @{term H} with arc type @{typ "'a \<times> nat \<times> 'a"}. Hence, we first characterize
  the existence of euler trail for the infinite arc type @{typ "'a \<times> nat \<times> 'a"}
  and transfer that result back to arbitrary arc types.
\<close>

lemma open_euler_infinite_label:
  fixes G :: "('a, 'a \<times> nat \<times> 'a) pre_digraph"
  assumes "fin_digraph G"
  assumes [simp]: "tail G = fst" "head G = snd o snd"
  assumes con: "connected G"
  assumes uv: "u \<in> verts G" "v \<in> verts G"
  assumes deg: "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
  assumes deg_in: "in_degree G u + 1 = out_degree G u"
  assumes deg_out: "out_degree G v + 1 = in_degree G v"
  shows "\<exists>p. pre_digraph.euler_trail G u p v"
proof -
  define label :: "'a \<times> nat \<times> 'a \<Rightarrow> nat" where [simp]: "label = fst o snd"

  interpret fin_digraph G by fact

  have "finite (label ` arcs G)" by auto
  moreover have "\<not>finite (UNIV :: nat set)" by blast
  ultimately obtain l where "l \<notin> label ` arcs G" by atomize_elim (rule ex_new_if_finite)

  from deg_in deg_out have "u \<noteq> v" by auto

  let ?e = "(v,l,u)"

  have e_notin:"?e \<notin> arcs G"
    using \<open>l \<notin> _\<close> by (auto simp: image_def)

  let ?H = "add_arc ?e"
    \<comment> \<open>We define a graph which has an closed euler trail\<close>

  have [simp]: "verts ?H = verts G" using uv by simp
  have [intro]: "\<And>a. compatible (add_arc a) G" by (simp add: compatible_def)

  interpret H: fin_digraph "add_arc a"
    rewrites "tail (add_arc a) = tail G" and "head (add_arc a) = head G"
      and "pre_digraph.cas (add_arc a) = cas"
      and "pre_digraph.awalk_verts (add_arc a) = awalk_verts"
     for a
      by unfold_locales (auto dest: wellformed intro: compatible_cas compatible_awalk_verts
          simp: verts_add_arc_conv)

  have "\<exists>u p. H.euler_trail ?e u p u"
  proof (rule H.closed_euler1)
    show "connected ?H"
    proof (rule H.connectedI)
      interpret sH: pair_fin_digraph "mk_symmetric ?H" ..
      fix u v assume "u \<in> verts ?H" "v \<in> verts ?H"
      with con have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v" by (auto simp: connected_def)
      moreover
      have "subgraph G ?H" by (auto simp: subgraph_def) unfold_locales
      ultimately show "u \<rightarrow>\<^sup>*\<^bsub>with_proj (mk_symmetric ?H)\<^esub> v"
        by (blast intro: sH.reachable_mono subgraph_mk_symmetric)
    qed (simp add: verts_add_arc_conv)
  next
    fix w assume "w \<in> verts ?H"
    then show "in_degree ?H w = out_degree ?H w"
      using deg deg_in deg_out e_notin
      apply (cases "w = u")
       apply (case_tac [!] "w = v")
         by (auto simp: in_degree_add_arc_iff out_degree_add_arc_iff)
  qed

  then obtain w p where Het: "H.euler_trail ?e w p w" by blast
  then have "?e \<in> set p" by (auto simp: pre_digraph.euler_trail_def)
  then obtain q r where p_decomp: "p = q @ [?e] @ r"
    by (auto simp: in_set_conv_decomp)
    \<comment> \<open>We show now that removing the additional arc of @{term ?H}
      from p yields an euler trail in G\<close>

  have "euler_trail u (r @ q) v"
  proof (unfold euler_trail_conv_connected[OF con], intro conjI)
    from Het have Ht': "H.trail ?e v (?e # r @ q) v"
      unfolding p_decomp H.euler_trail_def H.trail_def
      by (auto simp: p_decomp H.awalk_Cons_iff)
    then have "H.trail ?e u (r @ q) v" "?e \<notin> set (r @ q)"
      by (auto simp: H.trail_def H.awalk_Cons_iff)
    then show t': "trail u (r @ q) v"
      by (auto simp: trail_def H.trail_def awalk_def H.awalk_def)

    show "set (r @ q) = arcs G"
    proof -
      have "arcs G = arcs ?H - {?e}" using e_notin by auto
      also have "arcs ?H = set p" using Het
        by (auto simp: pre_digraph.euler_trail_def pre_digraph.trail_def)
      finally show ?thesis using \<open>?e \<notin> set _\<close> by (auto simp: p_decomp)
    qed
  qed
  then show ?thesis by blast
qed

context wf_digraph begin

lemma trail_app_isoI:
  assumes t: "trail u p v"
    and hom: "digraph_isomorphism hom"
  shows "pre_digraph.trail (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from t hom have i: "inj_on (iso_arcs hom) (set p)"
     unfolding trail_def digraph_isomorphism_def by (auto dest:subset_inj_on[where A="set p"])
  then have "distinct (map (iso_arcs hom) p) = distinct p"
    by (auto simp: distinct_map dest: inj_onD)
  with t hom show ?thesis
    by (auto simp: pre_digraph.trail_def awalk_app_isoI)
qed

lemma euler_trail_app_isoI:
  assumes t: "euler_trail u p v"
    and hom: "digraph_isomorphism hom"
  shows "pre_digraph.euler_trail (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  from t have "awalk u p v" by (auto simp: euler_trail_def trail_def)
  with assms show ?thesis
    by (simp add: pre_digraph.euler_trail_def trail_app_isoI awalk_verts_app_iso_eq)
qed


end

context fin_digraph begin

(* XXX: We can get rid of "u \<in> verts G" "v \<in> verts G" here and in @{thm open_euler_infinite_label} *)
theorem open_euler1:
  assumes "connected G"
  assumes "u \<in> verts G" "v \<in> verts G"
  assumes "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
  assumes "in_degree G u + 1 = out_degree G u"
  assumes "out_degree G v + 1 = in_degree G v"
  shows "\<exists>p. euler_trail u p v"
proof -
  obtain f and n :: nat where "f ` arcs G = {i. i < n}"
      and i: "inj_on f (arcs G)"
    by atomize_elim (rule finite_imp_inj_to_nat_seg, auto)

  define iso_f where "iso_f =
    \<lparr> iso_verts = id, iso_arcs = (\<lambda>a. (tail G a, f a, head G a)),
      head = snd o snd, tail = fst \<rparr>"
  have [simp]: "iso_verts iso_f = id" "iso_head iso_f = snd o snd" "iso_tail iso_f = fst"
    unfolding iso_f_def by auto
  have di_iso_f: "digraph_isomorphism iso_f" unfolding digraph_isomorphism_def iso_f_def
    by (auto intro: inj_onI wf_digraph dest: inj_onD[OF i])

  let ?iso_g = "inv_iso iso_f"
  have [simp]: "\<And>u. u \<in> verts G \<Longrightarrow> iso_verts ?iso_g u = u"
    by (auto simp: inv_iso_def fun_eq_iff the_inv_into_f_eq)

  let ?H = "app_iso iso_f G"
  interpret H: fin_digraph ?H using di_iso_f ..

  have "\<exists>p. H.euler_trail u p v"
    using di_iso_f assms i
    by (intro open_euler_infinite_label) (auto simp: connectedI_app_iso app_iso_eq)
  then obtain p where Het: "H.euler_trail u p v" by blast

  have "pre_digraph.euler_trail (app_iso ?iso_g ?H) (iso_verts ?iso_g u) (map (iso_arcs ?iso_g) p) (iso_verts ?iso_g v)"
    using Het by (intro H.euler_trail_app_isoI digraph_isomorphism_invI di_iso_f)
  then show ?thesis using di_iso_f \<open>u \<in> _\<close> \<open>v \<in> _\<close> by simp rule
qed

theorem open_euler2:
  assumes et: "euler_trail u p v" and "u \<noteq> v"
  shows "connected G \<and>
    (\<forall>w \<in> verts G. u \<noteq> w \<longrightarrow> v \<noteq> w \<longrightarrow> in_degree G w = out_degree G w) \<and>
    in_degree G u + 1 = out_degree G u \<and>
    out_degree G v + 1 = in_degree G v"
proof -
  from et have *: "trail u p v" "u \<in> verts G" "v \<in> verts G"
    by (auto simp: euler_trail_def trail_def awalk_hd_in_verts)

  from et have [simp]: "\<And>u. card (in_arcs G u \<inter> set p) = in_degree G u"
      "\<And>u. card (out_arcs G u \<inter> set p) = out_degree G u"
    by (auto simp: in_degree_def out_degree_def euler_trail_def intro: arg_cong[where f=card])

  from assms * show ?thesis
    by (auto simp: arc_set_balance_def elim: trail_arc_balanceE
        intro: euler_imp_connected)
qed

corollary open_euler:
  "(\<exists>u p v. euler_trail u p v \<and> u \<noteq> v) \<longleftrightarrow>
    connected G \<and> (\<exists>u v. u \<in> verts G \<and> v \<in> verts G \<and>
      (\<forall>w \<in> verts G. u \<noteq> w \<longrightarrow> v \<noteq> w \<longrightarrow> in_degree G w = out_degree G w) \<and>
      in_degree G u + 1 = out_degree G u \<and>
      out_degree G v + 1 = in_degree G v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain u p v where *: "euler_trail u p v" "u \<noteq> v"
    by auto
  then have "u \<in> verts G" "v \<in> verts G"
    by (auto simp: euler_trail_def trail_def awalk_hd_in_verts)
  then show ?R using open_euler2[OF *] by blast
next
  assume ?R
  then obtain u v where *:
    "connected G" "u \<in> verts G" "v \<in> verts G"
    "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
    "in_degree G u + 1 = out_degree G u"
    "out_degree G v + 1 = in_degree G v"
    by blast
  then have "u \<noteq> v" by auto
  from * show ?L by (metis open_euler1 \<open>u \<noteq> v\<close>)
qed

end

end
