theory Subdivision
imports
  Arc_Walk
  Digraph_Component
  Pair_Digraph
  Bidirected_Digraph
  Funpow
begin

section \<open>Subdivision on Digraphs\<close>

definition
  subdivision_step :: "('a, 'b) pre_digraph \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) pre_digraph \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a \<times> 'a \<times> 'a \<Rightarrow> 'b \<times> 'b \<times> 'b \<Rightarrow> bool"
where
  "subdivision_step G rev_G H rev_H \<equiv> \<lambda>(u, v, w) (uv, uw, vw).
      bidirected_digraph G rev_G
    \<and> bidirected_digraph H rev_H
    \<and> perm_restrict rev_H (arcs G) = perm_restrict rev_G (arcs H)
    \<and> compatible G H

    \<and> verts H = verts G \<union> {w}
    \<and> w \<notin> verts G

    \<and> arcs H = {uw, rev_H uw, vw, rev_H vw} \<union> arcs G - {uv, rev_G uv}
    \<and> uv \<in> arcs G
    \<and> distinct [uw, rev_H uw, vw, rev_H vw]
    \<and> arc_to_ends G uv = (u,v)
    \<and> arc_to_ends H uw = (u,w)
    \<and> arc_to_ends H vw = (v,w)
  "

inductive subdivision :: "('a,'b) pre_digraph \<times> ('b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) pre_digraph \<times> ('b \<Rightarrow> 'b) \<Rightarrow> bool"
  for biG where
    base: "bidirected_digraph (fst biG) (snd biG) \<Longrightarrow> subdivision biG biG"
  | divide: "\<lbrakk>subdivision biG biI; subdivision_step (fst biI) (snd biI) (fst biH) (snd biH) (u,v,w) (uv,uw,vw)\<rbrakk> \<Longrightarrow> subdivision biG biH"

lemma subdivision_induct[case_names base divide, induct pred: subdivision]:
  assumes "subdivision (G, rev_G) (H, rev_H)"
    and "bidirected_digraph G rev_G \<Longrightarrow> P G rev_G"
    and "\<And>I rev_I H rev_H u v w uv uw vw.
            subdivision (G, rev_G) (I, rev_I) \<Longrightarrow> P I rev_I \<Longrightarrow> subdivision_step I rev_I H rev_H (u, v, w) (uv, uw, vw) \<Longrightarrow> P H rev_H"
  shows "P H rev_H"
  using assms(1) by (induct biH\<equiv>"(H, rev_H)" arbitrary: H rev_H) (auto intro: assms(2,3))

lemma subdivision_base:
  "bidirected_digraph G rev_G \<Longrightarrow> subdivision (G, rev_G) (G, rev_G)"
  by (rule subdivision.base) simp

lemma subdivision_step_rev:
  assumes "subdivision_step G rev_G H rev_H (u, v, w) (uv, uw, vw)" "subdivision (H, rev_H) (I, rev_I)"
  shows "subdivision (G, rev_G) (I, rev_I)"
proof -
  have "bidirected_digraph (fst (G, rev_G)) (snd (G, rev_G))" using assms by (auto simp: subdivision_step_def)
  with assms(2,1) show ?thesis
    using assms(2,1) by induct (auto intro: subdivision.intros dest: subdivision_base)
qed

lemma subdivision_trans:
  assumes "subdivision (G, rev_G) (H, rev_H)" "subdivision (H, rev_H) (I, rev_I)"
  shows "subdivision (G, rev_G) (I, rev_I)"
  using assms by induction (auto intro: subdivision_step_rev)

locale subdiv_step =
  fixes G rev_G H rev_H u v w uv uw vw
  assumes subdiv_step: "subdivision_step G rev_G H rev_H (u, v, w) (uv, uw, vw)"

sublocale subdiv_step \<subseteq> G: bidirected_digraph G rev_G
  using subdiv_step unfolding subdivision_step_def by simp
sublocale subdiv_step \<subseteq> H: bidirected_digraph H rev_H
  using subdiv_step unfolding subdivision_step_def by simp

context subdiv_step begin

  (*XXX*)
  abbreviation (input) "vu \<equiv> rev_G uv"
  abbreviation (input) "wu \<equiv> rev_H uw"
  abbreviation (input) "wv \<equiv> rev_H vw"

  lemma subdiv_compat: "compatible G H"
    using subdiv_step by (simp add: subdivision_step_def)

  lemma arc_to_ends_eq: "arc_to_ends H = arc_to_ends G"
    using subdiv_compat by (simp add: compatible_def arc_to_ends_def fun_eq_iff)

  lemma head_eq: "head H = head G"
    using subdiv_compat by (simp add: compatible_def fun_eq_iff)

  lemma tail_eq: "tail H = tail G"
    using subdiv_compat by (simp add: compatible_def fun_eq_iff)

  lemma verts_H: "verts H = verts G \<union> {w}"
    using subdiv_step by (simp add: subdivision_step_def)

  lemma verts_G: "verts G = verts H - {w}"
    using subdiv_step by (auto simp: subdivision_step_def)

  lemma arcs_H: "arcs H = {uw, wu, vw, wv} \<union> arcs G - {uv, vu}"
    using subdiv_step by (simp add: subdivision_step_def)

  lemma not_in_verts_G: "w \<notin> verts G"
    using subdiv_step by (simp add: subdivision_step_def)

  lemma in_arcs_G: "{uv, vu} \<subseteq> arcs G"
    using subdiv_step by (simp add: subdivision_step_def)

  lemma not_in_arcs_H: "{uv,vu} \<inter> arcs H = {}"
    using arcs_H by auto

  lemma subdiv_ate:
      "arc_to_ends G uv = (u,v)"
      "arc_to_ends H uv = (u,v)"
      "arc_to_ends H uw = (u,w)"
      "arc_to_ends H vw = (v,w)"
    using subdiv_step subdiv_compat by (auto simp: subdivision_step_def arc_to_ends_def compatible_def)

  lemma subdiv_ends[simp]:
    "tail G uv = u" "head G uv = v" "tail H uv = u" "head H uv = v"
    "tail H uw = u" "head H uw = w" "tail H vw = v" "head H vw = w"
    using subdiv_ate by (auto simp: arc_to_ends_def)

  lemma subdiv_ends_G_rev[simp]:
    "tail G (vu) = v" "head G (vu) = u" "tail H (vu) = v" "head H (vu) = u"
    using in_arcs_G by (auto simp: tail_eq head_eq)

  lemma subdiv_distinct_verts0: "u \<noteq> w" "v \<noteq> w"
      using in_arcs_G not_in_verts_G using subdiv_ate by (auto simp: arc_to_ends_def dest: G.wellformed)

  lemma in_arcs_H: "{uw, wu, vw, wv} \<subseteq> arcs H"
  proof -
    { assume "uv = uw"
      then have "arc_to_ends H uv = arc_to_ends H uw" by simp
      then have "v = w" by (simp add: arc_to_ends_def)
    } moreover
    { assume "uv = vw"
      then have "arc_to_ends H uv = arc_to_ends H vw" by simp
      then have "v = w" by (simp add: arc_to_ends_def)
    } moreover
    { assume "vu = uw"
      then have "arc_to_ends H (vu) = arc_to_ends H uw" by simp
      then have "u = w" by (simp add: arc_to_ends_def)
    } moreover
    { assume "vu = vw"
      then have "arc_to_ends H (vu) = arc_to_ends H vw" by simp
      then have "u = w" by (simp add: arc_to_ends_def)
    } ultimately
    have "{uw,vw} \<subseteq> arcs H" unfolding arcs_H using subdiv_distinct_verts0 by auto
    then show ?thesis by auto
  qed

  lemma subdiv_ends_H_rev[simp]:
    "tail H (wu) = w" "tail H (wv) = w"
    "head H (wu) = u" "head H (wv) = v"
    using in_arcs_H subdiv_ate by simp_all

  lemma in_verts_G: "{u,v} \<subseteq> verts G"
    using in_arcs_G by (auto dest: G.wellformed)

  lemma not_in_arcs_G: "{uw, wu, vw, wv} \<inter> arcs G = {}"
  proof -
    note X = G.wellformed[simplified tail_eq[symmetric] head_eq[symmetric]]
    show ?thesis using not_in_verts_G in_arcs_H by (auto dest: X )
  qed

  lemma subdiv_distinct_arcs: "distinct [uv, vu, uw, wu, vw, wv]"
  proof -
    have "distinct [uw, wu, vw, wv]"
      using subdiv_step by (simp add: subdivision_step_def)
    moreover
    have "distinct [uv, vu]" using in_arcs_G G.arev_dom by auto
    moreover
    have "{uv, vu} \<inter> {uw, wu, vw, wv} = {}"
      using arcs_H in_arcs_H by auto
    ultimately show ?thesis by auto
  qed

  lemma arcs_G: "arcs G = arcs H \<union> {uv, vu} - {uw, wu, vw, wv}"
    using in_arcs_G not_in_arcs_G unfolding arcs_H by auto

  lemma subdiv_ate_H_rev:
    "arc_to_ends H (wu) = (w,u)"
    "arc_to_ends H (wv) = (w,v)"
    using in_arcs_H subdiv_ate by simp_all

  lemma adj_with_w: "u \<rightarrow>\<^bsub>H\<^esub> w" "w \<rightarrow>\<^bsub>H\<^esub> u" "v \<rightarrow>\<^bsub>H\<^esub> w" "w \<rightarrow>\<^bsub>H\<^esub> v"
    using in_arcs_H subdiv_ate by (auto intro: H.dominatesI[rotated])

  lemma w_reach: "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>H\<^esub> u" "v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v"
    using adj_with_w by auto

  lemma G_reach: "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    using subdiv_ate in_arcs_G by (simp add: G.dominatesI G.symmetric_reachable')+

  lemma out_arcs_w: "out_arcs H w = {wu, wv}"
    using subdiv_distinct_verts0 in_arcs_H
    by (auto simp: arcs_H) (auto simp: tail_eq verts_G dest: G.tail_in_verts)

  lemma out_degree_w: "out_degree H w = 2"
    using subdiv_distinct_arcs by (auto simp: out_degree_def out_arcs_w card_insert_if)

end

lemma subdivision_compatible:
  assumes "subdivision (G, rev_G) (H, rev_H)" shows "compatible G H"
  using assms by induct (auto simp: compatible_def subdivision_step_def)

lemma subdivision_bidir:
  assumes "subdivision (G, rev_G) (H, rev_H)"
  shows "bidirected_digraph H rev_H"
  using assms by induct (auto simp: subdivision_step_def)

lemma subdivision_choose_rev:
  assumes "subdivision (G, rev_G) (H, rev_H)" "bidirected_digraph H rev_H'"
  shows "\<exists>rev_G'. subdivision (G, rev_G') (H, rev_H')"
  using assms
proof (induction arbitrary: rev_H')
  case base
  then show ?case by (auto dest: subdivision_base)
next
  case (divide I rev_I H rev_H u v w uv uw vw)

  interpret subdiv_step I rev_I H rev_H u v w uv uw vw using divide by unfold_locales
  interpret H': bidirected_digraph H rev_H' by fact

  define rev_I' where "rev_I' x =
    (if x = uv then rev_I uv else if x = rev_I uv then uv else if x \<in> arcs I then rev_H' x else x)"
    for x

  have rev_H_injD: "\<And>x y z. rev_H' x = z \<Longrightarrow> rev_H' y = z \<Longrightarrow> x \<noteq> y \<Longrightarrow> False"
    by (metis H'.arev_eq_iff)

  have rev_H'_simps: "rev_H' uw = rev_H uw \<and> rev_H' vw = rev_H vw
    \<or> rev_H' uw = rev_H vw \<and> rev_H' vw = rev_H uw"
  proof -
    have "arc_to_ends H (rev_H' uw) = (w,u)" "arc_to_ends H (rev_H' vw) = (w,v)"
      using in_arcs_H by (auto simp: subdiv_ate)
    moreover
    have "\<And>x. x \<in> arcs H \<Longrightarrow> tail H x = w \<Longrightarrow> x \<in> {rev_H uw, rev_H vw}"
      using subdiv_distinct_verts0 not_in_verts_G by (auto simp: arcs_H) (simp add: tail_eq)
    ultimately
    have "rev_H' uw \<in> {rev_H uw, rev_H vw}" "rev_H' vw \<in> {rev_H uw, rev_H vw}"
      using in_arcs_H by auto
    then show ?thesis using in_arcs_H by (auto dest: rev_H_injD)
  qed

  have rev_H_uv: "rev_H' uv = uv" "rev_H' (rev_I uv) = rev_I uv"
    using not_in_arcs_H by (auto simp: H'.arev_eq)

  have bd_I': "bidirected_digraph I rev_I'"
  proof
    fix a
    have "\<And>a. a \<noteq> uv \<Longrightarrow> a \<noteq> rev_I uv \<Longrightarrow> a \<in> arcs I \<Longrightarrow> a \<in> arcs H"
      by (auto simp: arcs_H)
    then show "(a \<in> arcs I) = (rev_I' a \<noteq> a)"
      using in_arcs_G by (auto simp: rev_I'_def dest: G.arev_neq H'.arev_neq)
  next
    fix a
    have *: "\<And>a. rev_H' a = rev_I uv \<longleftrightarrow> a = rev_I uv"
      by (metis H'.arev_arev H'.arev_dom insert_disjoint(1) not_in_arcs_H)
    have **: "\<And>a. uv = rev_H' a \<longleftrightarrow> a = uv" using H'.arev_eq not_in_arcs_H by force
    have ***: "\<And>a. a \<in> arcs I \<Longrightarrow> rev_H' a \<in> arcs I"
      using rev_H'_simps  by (case_tac "a \<in> {uv,vu}") (fastforce simp: rev_H_uv, auto simp: arcs_G dest: rev_H_injD)
    show "rev_I' (rev_I' a) = a"
      by (auto simp: rev_I'_def H'.arev_eq rev_H_uv * ** ***)
  next
    fix a assume "a \<in> arcs I"
    then show "tail I (rev_I' a) = head I a"
      using in_arcs_G by (auto simp: rev_I'_def tail_eq[symmetric] head_eq[symmetric] arcs_H)
  qed
  moreover
  have "\<And>x. rev_H' x = uv \<longleftrightarrow> x = uv" "\<And>x. rev_H' x = rev_I uv \<longleftrightarrow> x = rev_I uv"
    using not_in_arcs_H by (auto dest: H'.arev_eq) (metis H'.arev_arev H'.arev_eq)
  then have "perm_restrict rev_H' (arcs I) = perm_restrict rev_I' (arcs H)"
    using not_in_arcs_H by (auto simp: rev_I'_def perm_restrict_def H'.arev_eq)
  ultimately
  have sds_I'H': "subdivision_step I rev_I' H rev_H' (u, v, w) (uv, uw, vw)"
    using divide(2,4) rev_H'_simps unfolding subdivision_step_def
    by (fastforce simp:  rev_I'_def)
  then have "subdivision (I, rev_I') (H, rev_H')" "\<exists>rev_G'. subdivision (G, rev_G') (I, rev_I')"
    using bd_I' divide by (auto intro: subdivision.intros dest: subdivision_base)
  then show ?case by (blast intro: subdivision_trans)
qed

lemma subdivision_verts_subset:
  assumes "subdivision (G,rev_G) (H,rev_H)" "x \<in> verts G"
  shows "x \<in> verts H"
  using assms by induct (auto simp: subdiv_step.verts_H subdiv_step_def)


subsection \<open>Subdivision on Pair Digraphs\<close>

text \<open>
  In this section, we introduce specialized rules for pair digraphs.
\<close>

abbreviation "subdivision_pair G H \<equiv> subdivision (with_proj G, swap_in (parcs G)) (with_proj H, swap_in (parcs H))"

lemma arc_to_ends_with_proj[simp]: "arc_to_ends (with_proj G) = id"
  by (auto simp: arc_to_ends_def)

context
begin

  text \<open>
    We use the @{verbatim inductive} command to define an inductive definition pair graphs.
    This is proven to be equivalent to @{const subdivision}.
    This allows us to transfer the rules proven by @{verbatim inductive} to @{const subdivision}.
    To spare the user confusion, we hide this new constant.
  \<close>

  private inductive pair_sd :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> bool"
    for G where
      base: "pair_bidirected_digraph G \<Longrightarrow> pair_sd G G"
    | divide: "\<And>e w H. \<lbrakk>e \<in> parcs H; w \<notin> pverts H; pair_sd G H\<rbrakk>
        \<Longrightarrow> pair_sd G (subdivide H e w)"

  private lemma bidirected_digraphI_pair_sd:
    assumes "pair_sd G H" shows "pair_bidirected_digraph H"
    using assms
  proof induct
    case base
    then show ?case by auto
  next
    case (divide e w H)
    interpret H: pair_bidirected_digraph H by fact
    from divide show ?case by (intro H.pair_bidirected_digraph_subdivide)
  qed

  private lemma subdivision_with_projI:
    assumes "pair_sd G H"
    shows "subdivision_pair G H"
    using assms
  proof induct
    case base
    then show ?case by (blast intro: pair_bidirected_digraph.bidirected_digraph subdivision_base)
  next
    case (divide e w H)

    obtain u v where "e = (u,v)" by (cases e)

    interpret H: pair_bidirected_digraph H
      using divide(3) by (rule bidirected_digraphI_pair_sd)
    interpret I: pair_bidirected_digraph "subdivide H e w"
      using divide(1,2) by (rule H.pair_bidirected_digraph_subdivide)

    have uvw: "u \<noteq> v" "u \<noteq> w" "v \<noteq> w"
      using divide by (auto simp: \<open>e = _\<close> dest: H.adj_not_same H.wellformed)

    have "subdivision (with_proj G, swap_in (parcs G)) (H, swap_in (parcs H))"
      using divide by auto
    moreover
    have *: "perm_restrict (swap_in (parcs (subdivide H e w))) (parcs H) = perm_restrict (swap_in (parcs H)) (parcs (subdivide H e w))"
      by (auto simp: perm_restrict_def fun_eq_iff swap_in_def)
    have "subdivision_step (with_proj H) (swap_in (arcs H)) (with_proj (subdivide H e w)) (swap_in (arcs (subdivide H e w)))
        (u, v, w) (e, (u,w), (v,w))"
      unfolding subdivision_step_def
      unfolding prod.simps with_proj_simps
      using divide uvw
      by (intro conjI H.bidirected_digraph I.bidirected_digraph *)
         (auto simp add: swap_in_def \<open>e = _\<close> compatibleI_with_proj)
    ultimately
    show ?case by (auto intro: subdivision.divide)
  qed

  private lemma subdivision_with_projD:
    assumes "subdivision_pair G H"
    shows "pair_sd G H"
    using assms
  proof (induct "with_proj H" "swap_in (parcs H)" arbitrary: H rule: subdivision_induct)
    case base
    interpret bidirected_digraph "with_proj G" "swap_in (parcs G)" by fact
    from base have "G = H" by (simp add: with_proj_def)
    with base show ?case
      by (auto intro: pair_sd.base pair_bidirected_digraphI_bidirected_digraph)
  next
    case (divide I rev_I u v w uv uw vw)
    define I' where "I' = \<lparr> pverts = verts I, parcs = arcs I \<rparr>"
    have "compatible G I " using \<open>subdivision (with_proj G, _) (I, _)\<close>
      by (rule subdivision_compatible)
    then have "tail I = fst" "head I = snd" by (auto simp: compatible_def)
    then have I: "I = I'" by (auto simp: I'_def)
    moreover
    from I have "rev_I = swap_in (parcs I')"
      using \<open>subdivision_step _ _ _ _ _ _\<close>
      by (simp add: subdivision_step_def bidirected_digraph_rev_conv_pair)
    ultimately
    have pd_sd: "pair_sd G I'" by (auto intro: divide.hyps)

    interpret sd: subdiv_step I' "swap_in (parcs I')" H "swap_in (parcs H)" u v w uv uw vw
      using \<open>subdivision_step _ _ _ _ _ _\<close> unfolding \<open>I = _\<close> \<open>rev_I = _\<close> by unfold_locales

    have ends: "uv = (u,v)" "uw = (u,w)" "vw = (v,w)"
      using sd.subdiv_ate by simp_all
    then have si_ends: "swap_in (parcs H) (u,w) = (w,u)" "swap_in (parcs H) (v,w) = (w,v)"
        "swap_in (parcs I') (u,v) = (v,u)"
      using sd.subdiv_ends_H_rev sd.subdiv_ends_G_rev by (auto simp: swap_in_def)

    have "parcs H = parcs I' - {(u, v), (v, u)} \<union> {(u, w), (w, u), (w, v), (v, w)}"
      using sd.in_arcs_G sd.not_in_arcs_G sd.arcs_H by (auto simp: si_ends ends)
    then have "H = subdivide I' uv w" using sd.verts_H by (simp add: ends subdivide.simps)
    then show ?case
      using sd.in_arcs_G sd.not_in_verts_G by (auto intro: pd_sd pair_sd.divide)
  qed

  private lemma subdivision_pair_conv:
    "pair_sd G H = subdivision_pair G H "
    by (metis subdivision_with_projD subdivision_with_projI)

  lemmas subdivision_pair_induct = pair_sd.induct[
      unfolded subdivision_pair_conv, case_names base divide, induct pred: pair_sd]

  lemmas subdivision_pair_base = pair_sd.base[unfolded subdivision_pair_conv]
  lemmas subdivision_pair_divide = pair_sd.divide[unfolded subdivision_pair_conv]

  lemmas subdivision_pair_intros = pair_sd.intros[unfolded subdivision_pair_conv]
  lemmas subdivision_pair_cases = pair_sd.cases[unfolded subdivision_pair_conv]

  lemmas subdivision_pair_simps = pair_sd.simps[unfolded subdivision_pair_conv]

  lemmas bidirected_digraphI_subdivision = bidirected_digraphI_pair_sd[unfolded subdivision_pair_conv]

end

lemma (in pair_graph) pair_graph_subdivision:
  assumes "subdivision_pair G H"
  shows "pair_graph H"
  using assms
by (induct rule: subdivision_pair_induct) (blast intro: pair_graph.pair_graph_subdivide divide)+


end
