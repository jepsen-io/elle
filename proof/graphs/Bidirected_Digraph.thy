theory Bidirected_Digraph
imports
  Digraph
  "HOL-Library.Permutations"
begin

section \<open>Bidirected Graphs\<close>

locale bidirected_digraph = wf_digraph G for G +
  fixes arev :: "'b \<Rightarrow> 'b"
  assumes arev_dom: "\<And>a. a \<in> arcs G \<longleftrightarrow> arev a \<noteq> a"
  assumes arev_arev_raw: "\<And>a. a \<in> arcs G \<Longrightarrow> arev (arev a) = a"
  assumes tail_arev[simp]: "\<And>a. a \<in> arcs G \<Longrightarrow> tail G (arev a) = head G a"

lemma (in wf_digraph) bidirected_digraphI:
  assumes arev_eq: "\<And>a. a \<notin> arcs G \<Longrightarrow> arev a = a"
  assumes arev_neq: "\<And>a. a \<in> arcs G \<Longrightarrow> arev a \<noteq> a"
  assumes arev_arev_raw: "\<And>a. a \<in> arcs G \<Longrightarrow> arev (arev a) = a"
  assumes tail_arev: "\<And>a. a \<in> arcs G \<Longrightarrow> tail G (arev a) = head G a"
  shows "bidirected_digraph G arev"
  using assms by unfold_locales (auto simp: permutes_def)

context bidirected_digraph begin

  lemma bidirected_digraph[intro!]: "bidirected_digraph G arev"
    by unfold_locales

  lemma arev_arev[simp]: "arev (arev a) = a"
    using arev_dom by (cases "a \<in> arcs G") (auto simp: arev_arev_raw)

  lemma arev_o_arev[simp]: "arev o arev = id"
    by (simp add: fun_eq_iff)

  lemma arev_eq: "a \<notin> arcs G \<Longrightarrow> arev a = a"
    by (simp add: arev_dom)

  lemma arev_neq: "a \<in> arcs G \<Longrightarrow> arev a \<noteq> a"
    by (simp add: arev_dom)

  lemma arev_in_arcs[simp]: "a \<in> arcs G \<Longrightarrow> arev a \<in> arcs G"
    by (metis arev_arev arev_dom)

  lemma head_arev[simp]:
    assumes "a \<in> arcs G" shows "head G (arev a) = tail G a"
  proof -
    from assms have "head G (arev a) = tail G (arev (arev a)) "
      by (simp only: tail_arev arev_in_arcs)
    then show ?thesis by simp
  qed

  lemma ate_arev[simp]:
    assumes "a \<in> arcs G" shows "arc_to_ends G (arev a) = prod.swap (arc_to_ends G a)"
    using assms by (auto simp: arc_to_ends_def)

  lemma bij_arev: "bij arev"
    using arev_arev by (metis bij_betw_imageI inj_on_inverseI surjI)

  lemma arev_permutes_arcs: "arev permutes arcs G"
    using arev_dom bij_arev by (auto simp: permutes_def bij_iff)

  lemma arev_eq_iff: "\<And>x y. arev x = arev y \<longleftrightarrow> x = y"
    by (metis arev_arev)

  lemma in_arcs_eq: "in_arcs G w = arev ` out_arcs G w"
    by auto (metis arev_arev arev_in_arcs image_eqI in_out_arcs_conv tail_arev)

  lemma inj_on_arev[intro!]: "inj_on arev S"
    by (metis arev_arev inj_on_inverseI)

  lemma even_card_loops:
    "even (card (in_arcs G w \<inter> out_arcs G w))" (is "even (card ?S)")
  proof -
    { assume "\<not>finite ?S"
      then have ?thesis by simp
    }
    moreover
    { assume A:"finite ?S"
      have "card ?S = card (\<Union>{{a,arev a} | a. a \<in> ?S})" (is "_ = card (\<Union> ?T)")
        by (rule arg_cong[where f=card]) (auto intro!: exI[where x="{x, arev x}" for x])
      also have "\<dots>= sum card ?T"
      proof (rule card_Union_disjoint)
        show "\<And>A. A\<in>{{a, arev a} |a. a \<in> ?S} \<Longrightarrow> finite A" by auto
        show "pairwise disjnt {{a, arev a} |a. a \<in> in_arcs G w \<inter> out_arcs G w}"
          unfolding pairwise_def disjnt_def
           by safe (simp_all add: arev_eq_iff)
      qed
      also have "\<dots> = sum (\<lambda>a. 2) ?T"
        by (intro sum.cong) (auto simp: card_insert_if dest: arev_neq)
      also have "\<dots> = 2 * card ?T" by simp
      finally have ?thesis by simp
    }
    ultimately
    show ?thesis by blast
  qed

end

(*XXX*)
sublocale bidirected_digraph \<subseteq> sym_digraph
proof (unfold_locales, unfold symmetric_def, intro symI)
  fix u v assume "u \<rightarrow>\<^bsub>G\<^esub> v"
  then obtain a where "a \<in> arcs G" "arc_to_ends G a = (u,v)" by (auto simp: arcs_ends_def)
  then have "arev a \<in> arcs G" "arc_to_ends G (arev a) = (v,u)"
    by (auto simp: arc_to_ends_def)
  then show "v \<rightarrow>\<^bsub>G\<^esub> u" by (auto simp: arcs_ends_def intro: rev_image_eqI)
qed



end
