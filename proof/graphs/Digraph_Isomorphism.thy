theory Digraph_Isomorphism imports
  Arc_Walk
  Digraph
  Digraph_Component
begin

section \<open>Isomorphisms of Digraphs\<close>

record ('a,'b,'aa,'bb) digraph_isomorphism =
  iso_verts :: "'a \<Rightarrow> 'aa"
  iso_arcs :: "'b \<Rightarrow> 'bb"
  iso_head :: "'bb \<Rightarrow> 'aa"
  iso_tail :: "'bb \<Rightarrow> 'aa"

definition (in pre_digraph) digraph_isomorphism :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> bool" where 
  "digraph_isomorphism hom \<equiv>
    wf_digraph G \<and>
    inj_on (iso_verts hom) (verts G) \<and>
    inj_on (iso_arcs hom) (arcs G) \<and>
    (\<forall>a \<in> arcs G. 
    iso_verts hom (tail G a) = iso_tail hom (iso_arcs hom a) \<and>
    iso_verts hom (head G a) = iso_head hom (iso_arcs hom a))"

definition (in pre_digraph) inv_iso :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> ('aa,'bb,'a,'b) digraph_isomorphism" where
  "inv_iso hom \<equiv> \<lparr>
    iso_verts = the_inv_into (verts G) (iso_verts hom),
    iso_arcs = the_inv_into (arcs G) (iso_arcs hom),
    iso_head = head G,
    iso_tail = tail G
    \<rparr>"

definition app_iso
    :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> ('aa,'bb) pre_digraph" where
  "app_iso hom G \<equiv> \<lparr> verts = iso_verts hom ` verts G, arcs = iso_arcs hom ` arcs G,
    tail = iso_tail hom, head = iso_head hom \<rparr>"

definition digraph_iso :: "('a,'b) pre_digraph \<Rightarrow> ('c,'d) pre_digraph \<Rightarrow> bool"  where
  "digraph_iso G H \<equiv> \<exists>f. pre_digraph.digraph_isomorphism G f \<and> H = app_iso f G"

lemma verts_app_iso: "verts (app_iso hom G) = iso_verts hom ` verts G"
  and arcs_app_iso: "arcs (app_iso hom G) = iso_arcs hom `arcs G"
  and tail_app_iso: "tail (app_iso hom G) = iso_tail hom"
  and head_app_iso: "head (app_iso hom G) = iso_head hom"
  by (auto simp: app_iso_def)

lemmas app_iso_simps[simp] = verts_app_iso arcs_app_iso tail_app_iso head_app_iso

context pre_digraph begin

lemma
  assumes "digraph_isomorphism hom"
  shows iso_verts_inv_iso: "\<And>u. u \<in> verts G \<Longrightarrow> iso_verts (inv_iso hom) (iso_verts hom u) = u"
    and iso_arcs_inv_iso: "\<And>a. a \<in> arcs G \<Longrightarrow> iso_arcs (inv_iso hom) (iso_arcs hom a) = a"
    and iso_verts_iso_inv: "\<And>u. u \<in> verts (app_iso hom G) \<Longrightarrow> iso_verts hom (iso_verts (inv_iso hom) u) = u"
    and iso_arcs_iso_inv: "\<And>a. a \<in> arcs (app_iso hom G) \<Longrightarrow> iso_arcs hom (iso_arcs (inv_iso hom) a) = a"
    and iso_tail_inv_iso: "iso_tail (inv_iso hom) = tail G"
    and iso_head_inv_iso: "iso_head (inv_iso hom) = head G"
    and verts_app_inv_iso:"iso_verts (inv_iso hom) ` iso_verts hom ` verts G = verts G"
    and arcs_app_inv_iso:"iso_arcs (inv_iso hom) ` iso_arcs hom ` arcs G = arcs G"
  using assms by (auto simp: inv_iso_def digraph_isomorphism_def the_inv_into_f_f)

lemmas iso_inv_simps[simp] =
   iso_verts_inv_iso iso_verts_iso_inv
   iso_arcs_inv_iso iso_arcs_iso_inv
   verts_app_inv_iso arcs_app_inv_iso
   iso_tail_inv_iso iso_head_inv_iso

lemma app_iso_inv[simp]:
  assumes "digraph_isomorphism hom"
  shows "app_iso (inv_iso hom) (app_iso hom G) = G"
  using assms by (intro pre_digraph.equality) (auto intro: rev_image_eqI)

lemma iso_verts_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "u \<in> verts G" "v \<in> verts G"
  shows "iso_verts hom u = iso_verts hom v \<longleftrightarrow> u = v"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

lemma iso_arcs_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "e1 \<in> arcs G" "e2 \<in> arcs G"
  shows "iso_arcs hom e1 = iso_arcs hom e2 \<longleftrightarrow> e1 = e2"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

lemma
  assumes "digraph_isomorphism hom" "e \<in> arcs G"
  shows iso_verts_tail: "iso_tail hom (iso_arcs hom e) = iso_verts hom (tail G e)"
    and iso_verts_head: "iso_head hom (iso_arcs hom e) = iso_verts hom (head G e)"
  using assms unfolding digraph_isomorphism_def by auto

lemma digraph_isomorphism_inj_on_arcs:
  "digraph_isomorphism hom \<Longrightarrow> inj_on (iso_arcs hom) (arcs G)"
  by (auto simp: digraph_isomorphism_def)

lemma digraph_isomorphism_inj_on_verts:
  "digraph_isomorphism hom \<Longrightarrow> inj_on (iso_verts hom) (verts G)"
  by (auto simp: digraph_isomorphism_def)

end

lemma (in wf_digraph) wf_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "wf_digraph (app_iso hom G)"
proof unfold_locales
  fix e assume "e \<in> arcs (app_iso hom G)"
  then obtain e' where e': "e' \<in> arcs G" "iso_arcs hom e' = e"
    by auto
  then have "iso_verts hom (head G e') \<in> verts (app_iso hom G)"
      "iso_verts hom (tail G e') \<in> verts (app_iso hom G)"
    by auto
  then show "tail (app_iso hom G) e \<in> verts (app_iso hom G)"
      "head (app_iso hom G) e \<in> verts (app_iso hom G)"
    using e' assms by (auto simp: iso_verts_tail iso_verts_head)
qed

lemma (in fin_digraph) fin_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "fin_digraph (app_iso hom G)"
proof -
  interpret H: wf_digraph "app_iso hom G" using assms ..
  show ?thesis by unfold_locales auto
qed

context wf_digraph begin

lemma digraph_isomorphism_invI:
  assumes "digraph_isomorphism hom" shows "pre_digraph.digraph_isomorphism (app_iso hom G) (inv_iso hom)"
proof (unfold pre_digraph.digraph_isomorphism_def, safe)
  show "inj_on (iso_verts (inv_iso hom)) (verts (app_iso hom G))"
      "inj_on (iso_arcs (inv_iso hom)) (arcs (app_iso hom G))"
    using assms unfolding pre_digraph.digraph_isomorphism_def inv_iso_def
    by (auto intro: inj_on_the_inv_into)
next
  show "wf_digraph (app_iso hom G)" using assms ..
next
  fix a assume "a \<in> arcs (app_iso hom G)"
  then obtain b where B: "a = iso_arcs hom b" "b \<in> arcs G"
    by auto

  with assms have [simp]:
      "iso_tail hom (iso_arcs hom b) = iso_verts hom (tail G b)"
      "iso_head hom (iso_arcs hom b) = iso_verts hom (head G b)"
      "inj_on (iso_arcs hom) (arcs G)"
      "inj_on (iso_verts hom) (verts G)"
    by (auto simp: digraph_isomorphism_def)

  from B show "iso_verts (inv_iso hom) (tail (app_iso hom G) a)
      = iso_tail (inv_iso hom) (iso_arcs (inv_iso hom) a)"
    by (auto simp: inv_iso_def the_inv_into_f_f)
  from B show "iso_verts (inv_iso hom) (head (app_iso hom G) a)
      = iso_head (inv_iso hom) (iso_arcs (inv_iso hom) a)"
    by (auto simp: inv_iso_def the_inv_into_f_f)
qed


lemma awalk_app_isoI:
  assumes "awalk u p v" and hom: "digraph_isomorphism hom"
  shows "pre_digraph.awalk (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (auto simp: awalk_simps H.awalk_simps iso_verts_head iso_verts_tail)
qed

lemma awalk_app_isoD:
  assumes w: "pre_digraph.awalk (app_iso hom G) u p v" and hom: "digraph_isomorphism hom"
  shows "awalk (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p) (iso_verts (inv_iso hom) v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (force simp: awalk_simps H.awalk_simps iso_verts_head iso_verts_tail)+
qed

lemma awalk_verts_app_iso_eq:
  assumes "digraph_isomorphism hom" and "awalk u p v"
  shows "pre_digraph.awalk_verts (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p)
    = map (iso_verts hom) (awalk_verts u p)"
  using assms
  by (induct p arbitrary: u)
     (auto simp: pre_digraph.awalk_verts.simps iso_verts_head iso_verts_tail awalk_Cons_iff)

(*
lemma awalk_verts_app_iso_eq':
  assumes hom: "digraph_isomorphism hom" and w: "pre_digraph.awalk (app_iso hom G) u p v"
  shows "pre_digraph.awalk_verts (app_iso hom G) u p
    = map (iso_verts hom) (awalk_verts (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p))"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  have w': "awalk (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p) (iso_verts (inv_iso hom) v)"
    using w hom by (rule awalk_app_isoD)
  have "pre_digraph.awalk_verts (app_iso hom G) u p =
      pre_digraph.awalk_verts (app_iso hom G) (iso_verts hom (iso_verts (inv_iso hom) u)) (map (iso_arcs hom) (map (iso_arcs (inv_iso hom)) p))"
    using hom w by (auto simp add: o_def subsetD cong: map_cong)
  also have "\<dots> = map (iso_verts hom) (awalk_verts (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p))"
    using hom w' by (rule awalk_verts_app_iso_eq)
  finally show ?thesis .
qed
*)

lemma arcs_ends_app_iso_eq:
  assumes "digraph_isomorphism hom"
  shows "arcs_ends (app_iso hom G) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` arcs_ends G"
  using assms by (auto simp: arcs_ends_conv image_image iso_verts_head iso_verts_tail
      intro!: rev_image_eqI)

lemma in_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` in_arcs G u"
  using assms unfolding in_arcs_def by (auto simp: iso_verts_head)

lemma out_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` out_arcs G u"
  using assms unfolding out_arcs_def by (auto simp: iso_verts_tail)

lemma in_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_degree (app_iso hom G) (iso_verts hom u) = in_degree G u"
  unfolding in_degree_def in_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (in_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemma out_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_degree (app_iso hom G) (iso_verts hom u) = out_degree G u"
  unfolding out_degree_def out_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (out_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemma in_arcs_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "in_arcs (app_iso hom G) u = iso_arcs hom ` in_arcs G (iso_verts (inv_iso hom) u)"
  using assms in_arcs_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma out_arcs_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "out_arcs (app_iso hom G) u = iso_arcs hom ` out_arcs G (iso_verts (inv_iso hom) u)"
  using assms out_arcs_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma in_degree_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "in_degree (app_iso hom G) u = in_degree G (iso_verts (inv_iso hom) u)"
  using assms in_degree_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma out_degree_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "out_degree (app_iso hom G) u = out_degree G (iso_verts (inv_iso hom) u)"
  using assms out_degree_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemmas app_iso_eq =
  awalk_verts_app_iso_eq
  arcs_ends_app_iso_eq
  in_arcs_app_iso_eq'
  out_arcs_app_iso_eq'
  in_degree_app_iso_eq'
  out_degree_app_iso_eq'

lemma reachableI_app_iso:
  assumes r: "u \<rightarrow>\<^sup>* v" and hom: "digraph_isomorphism hom"
  shows "(iso_verts hom u) \<rightarrow>\<^sup>*\<^bsub>app_iso hom G\<^esub> (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from r obtain p where "awalk u p v" by (auto simp: reachable_awalk)
  then have "H.awalk (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
    using hom by (rule awalk_app_isoI)
  then show ?thesis by (auto simp: H.reachable_awalk)
qed

lemma awalk_app_iso_eq:
  assumes hom: "digraph_isomorphism hom"
  assumes "u \<in> iso_verts hom ` verts G" "v \<in> iso_verts hom ` verts G" "set p \<subseteq> iso_arcs hom ` arcs G"
  shows "pre_digraph.awalk (app_iso hom G) u p v
    \<longleftrightarrow> awalk (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p) (iso_verts (inv_iso hom) v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (auto simp: awalk_simps H.awalk_simps iso_verts_head iso_verts_tail)
qed

lemma reachable_app_iso_eq:
  assumes hom: "digraph_isomorphism hom"
  assumes "u \<in> iso_verts hom ` verts G" "v \<in> iso_verts hom ` verts G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>app_iso hom G\<^esub> v \<longleftrightarrow> iso_verts (inv_iso hom) u \<rightarrow>\<^sup>* iso_verts (inv_iso hom) v" (is "?L \<longleftrightarrow> ?R")
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..

  show ?thesis
  proof
    assume ?L
    then obtain p where "H.awalk u p v" by (auto simp: H.reachable_awalk)
    moreover
    then have "set p \<subseteq> iso_arcs hom ` arcs G" by (simp add: H.awalk_def)
    ultimately
    show ?R using assms by (auto simp: awalk_app_iso_eq reachable_awalk)
  next
    assume ?R
    then obtain p0 where "awalk (iso_verts (inv_iso hom) u) p0 (iso_verts (inv_iso hom) v)"
      by (auto simp: reachable_awalk)
    moreover
    then have "set p0 \<subseteq> arcs G" by (simp add: awalk_def)
    define p where "p = map (iso_arcs hom) p0"
    have "set p \<subseteq> iso_arcs hom ` arcs G" "p0 = map (iso_arcs (inv_iso hom)) p"
      using \<open>set p0 \<subseteq> _\<close> hom by (auto simp: p_def map_idI subsetD)
    ultimately
    show ?L using assms by (auto simp: awalk_app_iso_eq[symmetric] H.reachable_awalk)
  qed
qed

lemma connectedI_app_iso:
  assumes c: "connected G" and hom: "digraph_isomorphism hom"
  shows "connected (app_iso hom G)"
proof -
  have *: "symcl (arcs_ends (app_iso hom G)) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` symcl (arcs_ends G)"
    using hom by (auto simp add: app_iso_eq symcl_def)
  { fix u v assume "(u,v) \<in> rtrancl_on (verts G) (symcl (arcs_ends G))"
    then have "(iso_verts hom u, iso_verts hom v) \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
    proof induct
      case (step x y)
      have "(iso_verts hom x, iso_verts hom y)
          \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
        using step by (rule_tac rtrancl_on_into_rtrancl_on[where b="iso_verts hom x"]) (auto simp: *)
      then show ?case
        by (rule rtrancl_on_trans) (rule step)
    qed auto }
  with c show ?thesis unfolding connected_conv by auto
qed

end

lemma digraph_iso_swap:
  assumes "wf_digraph G" "digraph_iso G H" shows "digraph_iso H G"
proof -
  from assms obtain f where "pre_digraph.digraph_isomorphism G f" "H = app_iso f G"
    unfolding digraph_iso_def by auto
  then have "pre_digraph.digraph_isomorphism H (pre_digraph.inv_iso G f)" "app_iso (pre_digraph.inv_iso G f) H = G"
    using assms by (simp_all add: wf_digraph.digraph_isomorphism_invI pre_digraph.app_iso_inv)
  then show ?thesis unfolding digraph_iso_def by auto
qed

definition
  o_iso :: "('c,'d,'e,'f) digraph_isomorphism \<Rightarrow> ('a,'b,'c,'d) digraph_isomorphism \<Rightarrow> ('a,'b,'e,'f) digraph_isomorphism"
where
  "o_iso hom2 hom1 = \<lparr>
    iso_verts = iso_verts hom2 o iso_verts hom1,
    iso_arcs = iso_arcs hom2 o iso_arcs hom1,
    iso_head = iso_head hom2,
    iso_tail = iso_tail hom2
    \<rparr>"

lemma digraph_iso_trans[trans]:
  assumes "digraph_iso G H" "digraph_iso H I" shows "digraph_iso G I"
proof -
  from assms obtain hom1 where "pre_digraph.digraph_isomorphism G hom1" "H = app_iso hom1 G"
    by (auto simp: digraph_iso_def)
  moreover
  from assms obtain hom2 where "pre_digraph.digraph_isomorphism H hom2" "I = app_iso hom2 H"
    by (auto simp: digraph_iso_def)
  ultimately
  have "pre_digraph.digraph_isomorphism G (o_iso hom2 hom1)" "I = app_iso (o_iso hom2 hom1) G"
    apply (auto simp: o_iso_def app_iso_def pre_digraph.digraph_isomorphism_def)
    apply (rule comp_inj_on)
    apply auto
    apply (rule comp_inj_on)
    apply auto
    done
  then show ?thesis by (auto simp: digraph_iso_def)
qed

lemma (in pre_digraph) digraph_isomorphism_subgraphI:
  assumes "digraph_isomorphism hom"
  assumes "subgraph H G"
  shows "pre_digraph.digraph_isomorphism H hom"
  using assms by (auto simp: pre_digraph.digraph_isomorphism_def subgraph_def compatible_def intro: subset_inj_on)

(* XXX move *)
lemma (in wf_digraph) verts_app_inv_iso_subgraph:
  assumes hom: "digraph_isomorphism hom" and "V \<subseteq> verts G"
  shows "iso_verts (inv_iso hom) ` iso_verts hom ` V = V"
proof -
  have "\<And>x. x \<in> V \<Longrightarrow> iso_verts (inv_iso hom) (iso_verts hom x) = x"
    using assms by auto
  then show ?thesis by (auto simp: image_image cong: image_cong)
qed

(* XXX move *)
lemma (in wf_digraph) arcs_app_inv_iso_subgraph:
  assumes hom: "digraph_isomorphism hom" and "A \<subseteq> arcs G"
  shows "iso_arcs (inv_iso hom) ` iso_arcs hom ` A = A"
proof -
  have "\<And>x. x \<in> A \<Longrightarrow> iso_arcs (inv_iso hom) (iso_arcs hom x) = x"
    using assms by auto
  then show ?thesis by (auto simp: image_image cong: image_cong)
qed

(* XXX move *)
lemma (in pre_digraph) app_iso_inv_subgraph[simp]:
  assumes "digraph_isomorphism hom" "subgraph H G"
  shows "app_iso (inv_iso hom) (app_iso hom H) = H"
proof -
  from assms interpret wf_digraph G by auto
  have "\<And>u. u \<in> verts H \<Longrightarrow> u \<in> verts G" "\<And>a. a \<in> arcs H \<Longrightarrow> a \<in> arcs G"
    using assms by auto
  with assms show ?thesis
    by (intro pre_digraph.equality) (auto simp: verts_app_inv_iso_subgraph
      arcs_app_inv_iso_subgraph compatible_def)
qed

lemma (in wf_digraph) app_iso_iso_inv_subgraph[simp]:
  assumes "digraph_isomorphism hom"
  assumes subg: "subgraph H (app_iso hom G)"
  shows "app_iso hom (app_iso (inv_iso hom) H) = H"
proof -
  have "\<And>u. u \<in> verts H \<Longrightarrow> u \<in> iso_verts hom ` verts G" "\<And>a. a \<in> arcs H \<Longrightarrow> a \<in> iso_arcs hom ` arcs G"
    using assms by (auto simp: subgraph_def)
  with assms show ?thesis
    by (intro pre_digraph.equality) (auto simp: compatible_def image_image cong: image_cong)
qed

lemma (in pre_digraph) subgraph_app_isoI':
  assumes hom: "digraph_isomorphism hom"
  assumes subg: "subgraph H H'" "subgraph H' G"
  shows "subgraph (app_iso hom H) (app_iso hom H')"
proof -
  have "subgraph H G" using subg by (rule subgraph_trans)
  then have "pre_digraph.digraph_isomorphism H hom" "pre_digraph.digraph_isomorphism H' hom"
    using assms by (auto intro: digraph_isomorphism_subgraphI)
  then show ?thesis
    using assms by (auto simp: subgraph_def wf_digraph.wf_digraphI_app_iso compatible_def
      intro: digraph_isomorphism_subgraphI)
qed

lemma (in pre_digraph) subgraph_app_isoI:
  assumes "digraph_isomorphism hom"
  assumes "subgraph H G"
  shows "subgraph (app_iso hom H) (app_iso hom G)"
  using assms by (auto intro: subgraph_app_isoI' wf_digraph.subgraph_refl)

lemma (in pre_digraph) app_iso_eq_conv:
  assumes "digraph_isomorphism hom"
  assumes "subgraph H1 G" "subgraph H2 G"
  shows "app_iso hom H1 = app_iso hom H2 \<longleftrightarrow> H1 = H2" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have "app_iso (inv_iso hom) (app_iso hom H1) = app_iso (inv_iso hom) (app_iso hom H2)"
    by simp
  with assms show ?R by auto
qed simp

lemma in_arcs_app_iso_cases:
  assumes "a \<in> arcs (app_iso hom G)"
  obtains a0 where "a = iso_arcs hom a0" "a0 \<in> arcs G"
  using assms by auto

lemma in_verts_app_iso_cases:
  assumes "v \<in> verts (app_iso hom G)"
  obtains v0 where "v = iso_verts hom v0" "v0 \<in> verts G"
  using assms by auto

lemma (in wf_digraph) max_subgraph_iso:
  assumes hom: "digraph_isomorphism hom"
  assumes subg: "subgraph H (app_iso hom G)"
  shows "pre_digraph.max_subgraph (app_iso hom G) P H
    \<longleftrightarrow> max_subgraph (P o app_iso hom) (app_iso (inv_iso hom) H)"
proof -
  have hom_inv: "pre_digraph.digraph_isomorphism (app_iso hom G) (inv_iso hom)"
    using hom by (rule digraph_isomorphism_invI)
  interpret aG: wf_digraph "app_iso hom G" using hom ..

  have *: "subgraph (app_iso (inv_iso hom) H) G"
    using hom pre_digraph.subgraph_app_isoI'[OF hom_inv subg aG.subgraph_refl] by simp
  define H0 where "H0 = app_iso (inv_iso hom) H"
  then have H0: "H = app_iso hom H0" "subgraph H0 G" 
    using hom subg \<open>subgraph _ G\<close> by (auto simp: )
    
  show ?thesis (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L then show ?R using assms H0
      by (auto simp: max_subgraph_def aG.max_subgraph_def pre_digraph.subgraph_app_isoI'
        subgraph_refl pre_digraph.app_iso_eq_conv)
  next
    assume ?R
    then show ?L
      using assms hom_inv pre_digraph.subgraph_app_isoI[OF hom_inv]
      apply (auto simp: max_subgraph_def aG.max_subgraph_def)
      apply (erule allE[of _ "app_iso (inv_iso hom) H'" for H'])
      apply (auto simp: pre_digraph.subgraph_app_isoI' pre_digraph.app_iso_eq_conv)
      done
  qed
qed

lemma (in pre_digraph) max_subgraph_cong:
  assumes "H = H'" "\<And>H''. subgraph H' H'' \<Longrightarrow> subgraph H'' G \<Longrightarrow> P H'' = P' H''"
  shows "max_subgraph P H = max_subgraph P' H'"
  using assms by (auto simp: max_subgraph_def intro: wf_digraph.subgraph_refl)

lemma (in pre_digraph) inj_on_app_iso:
  assumes hom: "digraph_isomorphism hom"
  assumes "S \<subseteq> {H. subgraph H G}"
  shows "inj_on (app_iso hom) S"
  using assms by (intro inj_onI) (subst (asm) app_iso_eq_conv, auto)



subsection \<open>Graph Invariants\<close>

context
  fixes G hom assumes hom: "pre_digraph.digraph_isomorphism G hom"
begin

  interpretation wf_digraph G using hom by (auto simp: pre_digraph.digraph_isomorphism_def)

  lemma card_verts_iso[simp]: "card (iso_verts hom ` verts G) = card (verts G)"
    using hom by (intro card_image digraph_isomorphism_inj_on_verts)

  lemma card_arcs_iso[simp]: "card (iso_arcs hom ` arcs G) = card (arcs G)"
    using hom by (intro card_image digraph_isomorphism_inj_on_arcs)

  lemma strongly_connected_iso[simp]: "strongly_connected (app_iso hom G) \<longleftrightarrow> strongly_connected G"
    using hom by (auto simp: strongly_connected_def reachable_app_iso_eq)

  lemma subgraph_strongly_connected_iso:
    assumes "subgraph H G"
    shows "strongly_connected (app_iso hom H) \<longleftrightarrow> strongly_connected H"
  proof -
    interpret H: wf_digraph H using \<open>subgraph H G\<close> ..
    have "H.digraph_isomorphism hom" using hom assms by (rule digraph_isomorphism_subgraphI)
    then show ?thesis
      using assms by (auto simp: strongly_connected_def H.reachable_app_iso_eq)
  qed

  lemma sccs_iso[simp]: "pre_digraph.sccs (app_iso hom G) = app_iso hom ` sccs" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?L"
    then have "subgraph x (app_iso hom G)"
      by (auto simp: pre_digraph.sccs_def)
    then show "x \<in> ?R"
      using \<open>x \<in> ?L\<close> hom by (auto simp: pre_digraph.sccs_altdef2 max_subgraph_iso
        subgraph_strongly_connected_iso cong: max_subgraph_cong  intro: rev_image_eqI)
  next
    fix x assume "x \<in> ?R"
    then obtain x0 where "x0 \<in> sccs" "x = app_iso hom x0" by auto
    then show "x \<in> ?L"
      using hom by (auto simp: pre_digraph.sccs_altdef2 max_subgraph_iso subgraph_app_isoI
        subgraphI_max_subgraph subgraph_strongly_connected_iso cong: max_subgraph_cong)
  qed

  lemma card_sccs_iso[simp]: "card (app_iso hom ` sccs) = card sccs"
    apply (rule card_image)
    using hom
    apply (rule inj_on_app_iso)
    apply auto
    done

end

end
