(* Title:  Shortest_Path.thy
   Author: Lars Noschinski, TU München
*)

theory Shortest_Path imports
  Arc_Walk
  Weighted_Graph
  "HOL-Library.Extended_Real"
begin

section \<open>Shortest Paths\<close>


context wf_digraph begin

(*Rename, as we are outside of any local context?*)
definition \<mu> where
  "\<mu> f u v \<equiv> INF p\<in> {p. awalk u p v}. ereal (awalk_cost f p)"

lemma shortest_path_inf:
  assumes "\<not>(u \<rightarrow>\<^sup>* v)"
  shows "\<mu> f u v = \<infinity>"
proof -
  have *: "{p. awalk u p v} = {}"
    using assms by (auto simp: reachable_awalk)
  show "\<mu> f u v = \<infinity>" unfolding \<mu>_def *
    by (simp add: top_ereal_def)
qed

lemma min_cost_le_walk_cost:
  assumes "awalk u p v" 
  shows "\<mu> c u v \<le> awalk_cost c p"
  using assms unfolding \<mu>_def by (auto intro: INF_lower2)

lemma pos_cost_pos_awalk_cost:
  assumes "awalk u p v"
  assumes pos_cost: "\<And>e. e \<in> arcs G \<Longrightarrow> c e \<ge> 0"
  shows "awalk_cost c p \<ge> 0"
using assms by (induct p arbitrary: u) (auto simp: awalk_Cons_iff)

fun mk_cycles_path :: "nat
  \<Rightarrow> 'b awalk \<Rightarrow> 'b awalk" where
    "mk_cycles_path 0 c = []"
  | "mk_cycles_path (Suc n) c = c @ (mk_cycles_path n c)"

lemma mk_cycles_path_awalk:
  assumes "awalk u c u"
  shows "awalk u (mk_cycles_path n c) u"
using assms by (induct n) (auto simp: awalk_Nil_iff)

lemma mk_cycles_awalk_cost:
  assumes "awalk u p u"
  shows "awalk_cost c (mk_cycles_path n p) = n * awalk_cost c p"
using assms proof (induct rule: mk_cycles_path.induct)
  case 1 show ?case by simp
next
  case (2 n p)
  have "awalk_cost c (mk_cycles_path (Suc n) p)
      = awalk_cost c (p @ (mk_cycles_path n p))"
    by simp
  also have "\<dots> = awalk_cost c p + real n * awalk_cost c p"
  proof (cases n)
    case 0 then show ?thesis by simp
  next
    case (Suc n') then show ?thesis
      using 2 by simp
  qed
  also have "\<dots> = real (Suc n) * awalk_cost c p"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma inf_over_nats:
  fixes a c :: real
  assumes "c < 0"
  shows "(INF (i :: nat). ereal (a + i * c)) = - \<infinity>"
proof (rule INF_eqI)
  fix i :: nat show "- \<infinity> \<le> a + real i * c" by simp
next
  fix y :: ereal
  assume "\<And>(i :: nat). i \<in> UNIV \<Longrightarrow> y \<le> a + real i * c"
  then have l_assm: "\<And>i::nat. y \<le> a + real i * c" by simp

  show "y \<le> - \<infinity>"
  proof (subst ereal_infty_less_eq, rule ereal_bot)
    fix B :: real
    obtain real_x where "a + real_x * c \<le> B" using \<open>c < 0\<close>
      by atomize_elim
         (rule exI[where x="(- abs B -a)/c"], auto simp: field_simps)
    obtain x :: nat where "a + x * c \<le> B"
    proof (atomize_elim, intro exI[where x="nat(ceiling real_x)"] conjI)
      have "real (nat(ceiling real_x)) * c \<le> real_x * c"
        using \<open>c < 0\<close> by (simp add: real_nat_ceiling_ge)
      then show "a + nat(ceiling real_x) * c \<le> B"
        using \<open>a + real_x * c \<le> B\<close> by simp
    qed
    then show "y \<le> ereal B"
    proof -
      have "ereal (a + x * c) \<le> ereal B"
        using \<open>a + x * c \<le> B\<close> by simp
      with l_assm show ?thesis by (rule order_trans)
    qed
  qed
qed

lemma neg_cycle_imp_inf_\<mu>:
  assumes walk_p: "awalk u p v"
  assumes walk_c: "awalk w c w"
  assumes w_in_p: "w \<in> set (awalk_verts u p)"
  assumes "awalk_cost f c < 0"
  shows "\<mu> f u v = -\<infinity>"
proof -
  from w_in_p obtain xs ys where pv_decomp: "awalk_verts u p = xs @ w # ys"
    by (auto simp: in_set_conv_decomp)

  define q r where "q = take (length xs) p" and "r = drop (length xs) p"
  define ext_p where "ext_p n = q @ mk_cycles_path n c @ r" for n

  have ext_p_cost: "\<And>n. awalk_cost f (ext_p n)
      = (awalk_cost f q + awalk_cost f r) + n * awalk_cost f c"
    using \<open>awalk w c w\<close>
    by (auto simp: ext_p_def intro: mk_cycles_awalk_cost)

  from q_def r_def have "awlast u q = w"
    using pv_decomp walk_p by (auto simp: awalk_verts_take_conv elim!: awalkE)
  moreover
  from q_def r_def have "awalk u (q @ r) v"
    using walk_p by simp
  ultimately
  have "awalk u q w" "awalk w r v" "\<And>n. awalk w (mk_cycles_path n c) w"
    using walk_c
    by (auto simp: intro: mk_cycles_path_awalk)
  then have "\<And>n. awalk u (ext_p n) v"
    unfolding ext_p_def by (blast intro: awalk_appendI)
  then have "{ext_p i|i. i \<in> UNIV} \<subseteq> {p. awalk u p v}"
    by auto
  then have "(INF p\<in>{p. awalk u p v}. ereal (awalk_cost f p))
      \<le> (INF p\<in> {ext_p i|i. i \<in> UNIV}. ereal (awalk_cost f p))"
    by (auto intro: INF_superset_mono)
  also have "\<dots> = (INF i\<in> UNIV. ereal (awalk_cost f (ext_p i)))"
    by (rule arg_cong[where f=Inf], auto)
  also have "\<dots> = - \<infinity>" unfolding ext_p_cost 
    by (rule inf_over_nats[OF \<open>awalk_cost f c < 0\<close>])
  finally show ?thesis unfolding \<mu>_def by simp
qed

lemma walk_cheaper_path_imp_neg_cyc:
  assumes p_props: "awalk u p v"
  assumes less_path_\<mu>: "awalk_cost f p < (INF p\<in> {p. apath u p v}. ereal (awalk_cost f p))"
  shows "\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0"
proof -
  define path_\<mu> where "path_\<mu> = (INF p\<in> {p. apath u p v}. ereal (awalk_cost f p))"
  then have "awalk u p v" and "awalk_cost f p < path_\<mu>"
    using p_props less_path_\<mu> by simp_all
  then show ?thesis
  proof (induct rule: awalk_to_apath_induct)
    case (path p) then have "apath u p v" by (auto simp: apath_def)
    then show ?case using path.prems by (auto simp: path_\<mu>_def dest: not_mem_less_INF)
  next
    case (decomp p q r s)
    then obtain w where p_props: "p = q @ r @ s" "awalk u q w" "awalk w r w" "awalk w s v"
      by (auto elim: awalk_cyc_decompE)
    then have "awalk u (q @ s) v"
      using \<open>awalk u p v\<close> by (auto simp: awalk_appendI)
    then have verts_ss: "set (awalk_verts u (q @ s)) \<subseteq> set (awalk_verts u p)"
      using \<open>awalk u p v\<close> \<open>p = q @ r @ s\<close> by (auto simp: set_awalk_verts)

    show ?case
    proof (cases "ereal (awalk_cost f (q @ s)) < path_\<mu>")
      case True then have "\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u (q @ s)) \<and> awalk_cost f c < 0"
        by (rule decomp)
      then show ?thesis using verts_ss by auto
    next
      case False
      note \<open>awalk_cost f p < path_\<mu>\<close>
      also have "path_\<mu> \<le> awalk_cost f (q @ s)"
        using False by simp
      finally have "awalk_cost f r < 0" using \<open>p = q @ r @ s\<close> by simp
      moreover
      have "w \<in> set (awalk_verts u q)" using \<open>awalk u q w\<close> by auto
      then have "w \<in> set (awalk_verts u p)"
        using \<open>awalk u p v\<close> \<open>awalk u q w\<close> \<open>p = q @ r @ s\<close>
        by (auto simp: set_awalk_verts)    
      ultimately
      show ?thesis using \<open>awalk w r w\<close> by auto
    qed
  qed
qed

lemma (in fin_digraph) neg_inf_imp_neg_cyc:
  assumes inf_mu: "\<mu> f u v = - \<infinity>"
  shows "\<exists>p. awalk u p v \<and> (\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0)"
proof -
  define path_\<mu> where "path_\<mu> = (INF s\<in>{p. apath u p v}. ereal (awalk_cost f s))"

  have awalks_ne: "{p. awalk u p v} \<noteq> {}"
    using inf_mu unfolding \<mu>_def by safe (simp add: top_ereal_def)
  then have paths_ne: "{p. apath u p v} ~= {}"
    by (auto intro: apath_awalk_to_apath)

  obtain p where "apath u p v" "awalk_cost f p = path_\<mu>"
  proof -
    obtain p where "p \<in> {p. apath u p v}" "awalk_cost f p = path_\<mu>"
    using finite_INF_in[OF apaths_finite paths_ne, of "awalk_cost f"]
      by (auto simp: path_\<mu>_def)
    then show ?thesis using that by auto
  qed
  then have "path_\<mu> \<noteq> -\<infinity>" by auto
  then have "\<mu> f u v < path_\<mu>" using inf_mu by simp
  then obtain pw where p_def: "awalk u pw v" "awalk_cost f pw < path_\<mu>"
    by atomize_elim (auto simp: \<mu>_def INF_less_iff)
  then have "\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u pw) \<and> awalk_cost f c < 0"
    by (intro walk_cheaper_path_imp_neg_cyc) (auto simp: path_\<mu>_def)
  with \<open>awalk u pw v\<close> show ?thesis by auto
qed

lemma (in fin_digraph) no_neg_cyc_imp_no_neg_inf:
  assumes no_neg_cyc: "\<And>p. awalk u p v
    \<Longrightarrow> \<not>(\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0)"
  shows "- \<infinity> < \<mu> f u v"
proof (intro ereal_MInfty_lessI notI)
  assume "\<mu> f u v = - \<infinity>"
  then obtain p where p_props: "awalk u p v"
    and ex_cyc: "\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0"
    by atomize_elim (rule neg_inf_imp_neg_cyc)
  then show False using no_neg_cyc by blast
qed

lemma \<mu>_reach_conv:
  "\<mu> f u v < \<infinity> \<longleftrightarrow> u \<rightarrow>\<^sup>* v"
proof
  assume "\<mu> f u v < \<infinity>"
  then have "{p. awalk u p v} \<noteq> {}"
    unfolding \<mu>_def by safe (simp add: top_ereal_def)
  then show "u \<rightarrow>\<^sup>* v" by (simp add: reachable_awalk)
next
  assume "u \<rightarrow>\<^sup>* v"
  then obtain p where p_props: "apath u p v"
    by (metis reachable_awalk apath_awalk_to_apath)
  then have "{p} \<subseteq> {p. apath u p v}" by simp
  then have "\<mu> f u v \<le> (INF p\<in> {p}. ereal (awalk_cost f p))"
    unfolding \<mu>_def by (intro INF_superset_mono) (auto simp: apath_def)
  also have "\<dots> < \<infinity>" by (simp add: min_def)
  finally show "\<mu> f u v < \<infinity>" .
qed

lemma awalk_to_path_no_neg_cyc_cost:
  assumes p_props:"awalk u p v"
  assumes no_neg_cyc: "\<not> (\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0)"
  shows "awalk_cost f (awalk_to_apath p) \<le> awalk_cost f p"
using assms
proof (induct rule: awalk_to_apath_induct)
  case path then show ?case by (auto simp: awalk_to_apath.simps)
next
  case (decomp p q r s)
  from decomp(2,3) have "is_awalk_cyc_decomp p (q,r,s)"
    using awalk_cyc_decomp_has_prop[OF decomp(1)] by auto
  then have decomp_props: "p = q @ r @ s" "\<exists>w. awalk w r w" by auto

  have "awalk_cost f (awalk_to_apath p) = awalk_cost f (awalk_to_apath (q @ s))"
    using decomp by (auto simp: step_awalk_to_apath[of _ p _ q r s])
  also have "\<dots> \<le> awalk_cost f (q @ s)"
  proof -
    have "awalk u (q @ s) v"
      using \<open>awalk u p v\<close> decomp_props by (auto dest!: awalk_ends_eqD)
    then have "set (awalk_verts u (q @ s)) \<subseteq> set (awalk_verts u p)"
      using \<open>awalk u p v\<close> \<open>p = q @ r @ s\<close>
      by (auto simp add: set_awalk_verts)
    then show ?thesis using decomp.prems by (intro decomp.hyps) auto
  qed
  also have "\<dots> \<le> awalk_cost f p"
  proof -
    obtain w where "awalk u q w" "awalk w r w" "awalk w s v"
      using decomp by (auto elim: awalk_cyc_decompE)
    then have "w \<in> set (awalk_verts u q)" by auto
    then have "w \<in> set (awalk_verts u p)"
      using \<open>p = q @ r @ s\<close> \<open>awalk u p v\<close> \<open>awalk u q w\<close>
      by (auto simp add: set_awalk_verts)
    then have "0 \<le> awalk_cost f r" using \<open>awalk w r w\<close>
      using decomp.prems by (auto simp: not_less)
    then show ?thesis using \<open>p = q @ r @ s\<close> by simp
  qed
  finally show ?case .
qed

lemma (in fin_digraph) no_neg_cyc_reach_imp_path:
  assumes reach: "u \<rightarrow>\<^sup>* v"
  assumes no_neg_cyc: "\<And>p. awalk u p v
    \<Longrightarrow> \<not>(\<exists>w c. awalk w c w \<and> w \<in> set (awalk_verts u p) \<and> awalk_cost f c < 0)"
  shows "\<exists>p. apath u p v \<and> \<mu> f u v = awalk_cost f p"
proof -
  define set_walks where "set_walks = {p. awalk u p v}"
  define set_paths where "set_paths = {p. apath u p v}"

  have "set_paths \<noteq> {}"
  proof -
    obtain p where "apath u p v"
      using reach by (metis apath_awalk_to_apath reachable_awalk)
    then show ?thesis unfolding set_paths_def by blast
  qed

  have "\<mu> f u v = (INF p\<in> set_walks. ereal (awalk_cost f p))"
    unfolding \<mu>_def set_walks_def by simp
  also have "\<dots> = (INF p\<in> set_paths. ereal (awalk_cost f p))"
  proof (rule antisym)
    have "awalk_to_apath ` set_walks \<subseteq> set_paths"
      unfolding set_walks_def set_paths_def
      by (intro subsetI) (auto elim: apath_awalk_to_apath)
    then have "(INF p\<in> set_paths. ereal (awalk_cost f p))
      \<le> (INF p\<in> awalk_to_apath ` set_walks. ereal (awalk_cost f p))"
      by (rule INF_superset_mono) simp
    also have "\<dots> = (INF p\<in> set_walks. ereal (awalk_cost f (awalk_to_apath p)))"
      by (simp add: image_comp)
    also have "\<dots> \<le> (INF p\<in> set_walks. ereal (awalk_cost f p))"
    proof -
      { fix p assume "p \<in> set_walks"
        then have "awalk u p v" by (auto simp: set_walks_def)
        then have "awalk_cost f (awalk_to_apath p) \<le> awalk_cost f p"
          using no_neg_cyc
          using no_neg_cyc and awalk_to_path_no_neg_cyc_cost
          by auto }
      then show ?thesis by (intro INF_mono) auto
    qed
    finally show
      "(INF p\<in> set_paths. ereal (awalk_cost f p))
      \<le> (INF p\<in> set_walks. ereal (awalk_cost f p))" by simp

    have "set_paths \<subseteq> set_walks"
      unfolding set_paths_def set_walks_def by (auto simp: apath_def)
    then show "(INF p\<in> set_walks. ereal (awalk_cost f p))
      \<le> (INF p\<in> set_paths. ereal (awalk_cost f p))"
      by (rule INF_superset_mono) simp
  qed
  also have "\<dots> \<in> (\<lambda>p. ereal (awalk_cost f p)) ` set_paths"
    using apaths_finite \<open>set_paths \<noteq> {}\<close>
    by (intro finite_INF_in) (auto simp: set_paths_def)
  finally show ?thesis
    by (simp add: set_paths_def image_def)
qed

lemma (in fin_digraph) min_cost_awalk:
  assumes reach: "u \<rightarrow>\<^sup>* v"
  assumes pos_cost: "\<And>e. e \<in> arcs G \<Longrightarrow> c e \<ge> 0"
  shows "\<exists>p. apath u p v \<and> \<mu> c u v = awalk_cost c p"
proof -
  have pc: "\<And>u p v. awalk u p v \<Longrightarrow> 0 \<le> awalk_cost c p"
    using pos_cost_pos_awalk_cost pos_cost by auto 

  from reach show ?thesis
    by (rule no_neg_cyc_reach_imp_path) (auto simp: not_less intro: pc)
qed

lemma (in fin_digraph) pos_cost_mu_triangle:
  assumes pos_cost: "\<And>e. e \<in> arcs G \<Longrightarrow> c e \<ge> 0" (* introduce predicate? *)
  assumes e_props: "arc_to_ends G e = (u,v)" "e \<in> arcs G"
  shows "\<mu> c s v \<le> \<mu> c s u + c e"
proof cases
  assume "\<mu> c s u = \<infinity>" then show ?thesis by simp
next
  assume "\<mu> c s u \<noteq> \<infinity>"
  then have "{p. awalk s p u} \<noteq> {}"
    unfolding \<mu>_def by safe (simp add: top_ereal_def)
  then have "s \<rightarrow>\<^sup>* u" by (simp add: reachable_awalk)
  with pos_cost
  obtain p where p_props: "apath s p u" 
      and p_cost: "\<mu> c s u = awalk_cost c p"
    by (metis min_cost_awalk)

  have "awalk u [e] v"
    using e_props by (auto simp: arc_to_ends_def awalk_simps)
  with \<open>apath s p u\<close>
  have "awalk s (p @ [e]) v"
    by (auto simp: apath_def awalk_appendI)
  then have "\<mu> c s v \<le> awalk_cost c (p @ [e])"
    by (rule min_cost_le_walk_cost)
  also have "\<dots> \<le> awalk_cost c p + c e" by simp
  also have "\<dots> \<le> \<mu> c s u + c e" using p_cost by simp
  finally show ?thesis .
qed

lemma (in fin_digraph) mu_exact_triangle:
  assumes "v \<noteq> s"
  assumes "s \<rightarrow>\<^sup>* v"
  assumes nonneg_arcs: "\<And>e. e \<in> arcs G \<Longrightarrow> 0 \<le> c e"
  obtains u e where "\<mu> c s v = \<mu> c s u + c e" and "arc e (u,v)"
proof -
  obtain p where p_path: "apath s p v"
    and p_cost: "\<mu> c s v = awalk_cost c p"
    using assms by (metis min_cost_awalk)
  then obtain e p' where p'_props: "p = p' @ [e]" using \<open>v \<noteq> s\<close>
    by (cases p rule: rev_cases) (auto simp: apath_def)
  then obtain u where "awalk s p' u" "awalk u [e] v"
    using \<open>apath s p v\<close> by (auto simp: apath_def)
  then have mu_le: "\<mu> c s v \<le> \<mu> c s u + c e" and arc: "arc e (u,v)"
    using nonneg_arcs by (auto intro!: pos_cost_mu_triangle simp: arc_to_ends_def arc_def)

  have "\<mu> c s u + c e \<le> ereal (awalk_cost c p') + ereal (c e)"
    using \<open>awalk s p' u\<close>
    by (fast intro: add_right_mono min_cost_le_walk_cost)
  also have "\<dots> = awalk_cost c p" using p'_props by simp
  also have "\<dots> = \<mu> c s v" using p_cost by simp
  finally
  have "\<mu> c s v = \<mu> c s u + c e" using mu_le by auto
  then show ?thesis using arc ..
qed

lemma (in fin_digraph) mu_exact_triangle_Ex:
  assumes "v \<noteq> s"
  assumes "s \<rightarrow>\<^sup>* v"
  assumes "\<And>e. e \<in> arcs G \<Longrightarrow> 0 \<le> c e"
  shows "\<exists>u e. \<mu> c s v = \<mu> c s u + c e \<and> arc e (u,v)"
using assms by (metis mu_exact_triangle)

lemma (in fin_digraph) mu_Inf_triangle:
  assumes "v \<noteq> s"
  assumes "\<And>e. e \<in> arcs G \<Longrightarrow> 0 \<le> c e"
  shows "\<mu> c s v = Inf {\<mu> c s u + c e | u e. arc e (u, v)}" (is "_ = Inf ?S")
proof cases
  assume "s \<rightarrow>\<^sup>* v"
  then obtain u e where "\<mu> c s v = \<mu> c s u + c e" "arc e (u,v)"
    using assms by (metis mu_exact_triangle)
  then have "Inf ?S \<le> \<mu> c s v" by (auto intro: Complete_Lattices.Inf_lower)
  also have "\<dots> \<le> Inf ?S" using assms(2)
    by (auto intro!: Complete_Lattices.Inf_greatest pos_cost_mu_triangle
      simp: arc_def arc_to_ends_def)
  finally show ?thesis by simp
next
  assume "\<not>s \<rightarrow>\<^sup>* v"
  then have "\<mu> c s v = \<infinity>" by (metis shortest_path_inf)
  define S where "S = ?S"
  show "\<mu> c s v = Inf S"
  proof cases
    assume "S = {}"
    then show ?thesis unfolding \<open>\<mu> c s v = \<infinity>\<close>
      by (simp add: top_ereal_def)
  next
    assume "S \<noteq> {}"
    { fix x assume "x \<in> S"
      then obtain u e where "arc e (u,v)" and x_val: "x = \<mu> c s u + c e"
        unfolding S_def by auto
      then have "\<not>s \<rightarrow>\<^sup>* u" using \<open>\<not> s \<rightarrow>\<^sup>* v\<close> by (metis reachable_arc_trans)
      then have "\<mu> c s u + c e= \<infinity>" by (simp add: shortest_path_inf)
      then have "x = \<infinity>" using x_val by simp }
    then have "S = {\<infinity>}" using \<open>S \<noteq> {}\<close> by auto
    then show ?thesis using \<open>\<mu> c s v = \<infinity>\<close> by (simp add: min_def)
  qed
qed

end

end
