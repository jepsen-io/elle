theory Funpow
imports
  "HOL-Library.FuncSet"
  "HOL-Library.Permutations"
begin

section \<open>Auxiliary Lemmas about @{term "(^^)"}\<close>

lemma funpow_simp_l: "f ((f ^^ n) x) = (f ^^ Suc n) x"
  by (metis comp_apply funpow.simps(2))

lemma funpow_add_app: "(f ^^ n) ((f ^^ m) x) = (f ^^ (n + m)) x"
  by (metis comp_apply funpow_add)

lemma funpow_mod_eq:
  assumes "(f ^^ n) x = x" "0 < n" shows "(f ^^ (m mod n)) x = (f ^^ m) x"
proof (induct m rule: less_induct)
  case (less m)
  { assume "m < n" then have ?case by simp }
  moreover
  { assume "m = n" then have ?case by (simp add: \<open>_ = x\<close>)}
  moreover
  { assume "n < m"
    then have "m - n < m" "0 < m - n"  using \<open>0 < n\<close> by arith+

    have "(f ^^ (m mod n)) x = (f ^^ ((m - n) mod n)) x"
      using \<open>0 < m - n\<close> by (simp add: mod_geq)
    also have "\<dots> = (f ^^ (m - n)) x"
      using \<open>m - n < m\<close> by (rule less)
    also have "\<dots> = (f ^^ (m - n)) ((f ^^ n) x)"
      by (simp add: assms)
    also have "\<dots> = (f ^^ m) x"
      using \<open>0 < m - n\<close> by (simp add: funpow_add_app)
    finally have ?case . }
  ultimately show ?case by (metis linorder_neqE_nat)
qed

lemma id_funpow_id:
  assumes "f x = x" shows "(f ^^ n) x = x"
  using assms by (induct n) auto

lemma inv_id_abs[simp]: "inv (\<lambda>a. a) = id" unfolding id_def[symmetric] by simp

lemma inj_funpow:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "inj f" shows "inj (f ^^ n)"
proof (induct n)
  case 0 then show ?case by (auto simp: id_def[symmetric])
next
  case (Suc n) with assms show ?case unfolding funpow.simps by (rule inj_compose)
qed

lemma funpow_inj_finite:
  assumes "inj p" "finite {(p ^^ n) x |n. True}"
  shows "\<exists>n>0. (p ^^ n) x = x"
proof -
  have "\<not>finite {0::nat..}" by simp
  moreover
  have "{(p ^^ n) x |n. True} = (\<lambda>n. (p ^^ n) x) ` {0..}" by auto
  with assms have "finite \<dots>" by simp
  ultimately have "\<exists>n\<in>{0..}. \<not> finite {m \<in> {0..}. (p ^^ m) x = (p ^^ n) x}"
    by (rule pigeonhole_infinite)
  then obtain n where "\<not>finite {m. (p ^^ m) x = (p ^^ n) x}" by auto
  then have "\<not>finite ({m. (p ^^ m) x = (p ^^ n) x} - {n})" by auto
  then have "({m. (p ^^ m) x = (p ^^ n) x} - {n}) \<noteq> {}"
    by (metis finite.emptyI)
  then obtain m where m: "(p ^^ m) x = (p ^^ n) x" "m \<noteq> n" by auto

  { fix m n assume "(p ^^ n) x = (p ^^ m) x" "m < n"
    have "(p ^^ (n - m)) x = inv (p ^^ m) ((p ^^ m) ((p ^^ (n - m)) x))"
      using \<open>inj p\<close> by (simp add: inv_f_f inj_funpow)
    also have "((p ^^ m) ((p ^^ (n - m)) x)) = (p ^^ n) x"
      using \<open>m < n\<close> by (simp add: funpow_add_app)
    also have "inv (p ^^ m) \<dots> = x"
      using \<open>inj p\<close>  by (simp add: \<open>(p ^^ n) x = _\<close> inj_funpow)
    finally have "(p ^^ (n - m)) x = x" "0 < n - m"
      using \<open>m < n\<close> by auto }
  note general = this

  show ?thesis
  proof (cases m n rule: linorder_cases)
    case less
    then show ?thesis using general m by metis
  next
    case equal
    then show ?thesis using m by metis
  next
    case greater
    then show ?thesis using general m by metis
  qed
qed

lemma permutes_in_funpow_image:
  assumes "f permutes S" "x \<in> S"
  shows "(f ^^ n) x \<in> S"
  using assms by (induct n) (auto simp: permutes_in_image)

(* XXX move*)
lemma permutation_self:
  assumes "permutation p" shows "\<exists>n>0. (p ^^ n) x = x"
proof cases
  assume "p x = x" then show ?thesis by auto
next
  assume "p x \<noteq> x"
  from assms have "inj p" by (intro permutation_bijective bij_is_inj)
  { fix n
    from \<open>p x \<noteq> x\<close> have "(p ^^ Suc n) x \<noteq> (p ^^ n) x"
    proof (induct n arbitrary: x)
      case 0 then show ?case by simp
    next
      case (Suc n)
      have "p (p x) \<noteq> p x"
      proof (rule notI)
        assume "p (p x) = p x"
        then show False using \<open>p x \<noteq> x\<close> \<open>inj p\<close> by (simp add: inj_eq)
      qed
      have "(p ^^ Suc (Suc n)) x = (p ^^ Suc n) (p x)"
        by (metis funpow_simp_l funpow_swap1)
      also have "\<dots> \<noteq> (p ^^ n) (p x)"
        by (rule Suc) fact
      also have "(p ^^ n) (p x) = (p ^^ Suc n) x"
        by (metis funpow_simp_l funpow_swap1)
      finally show ?case by simp
    qed }
  then have "{(p ^^ n) x | n. True} \<subseteq> {x. p x \<noteq> x}"
    by auto
  then have "finite {(p ^^ n) x | n. True}"
    using permutation_finite_support[OF assms] by (rule finite_subset)
  with \<open>inj p\<close> show ?thesis by (rule funpow_inj_finite)
qed

(* XXX move *)
lemma (in -) funpow_invs:
  assumes "m \<le> n" and inv: "\<And>x. f (g x) = x"
  shows "(f ^^ m) ((g ^^ n) x) = (g ^^ (n - m)) x"
  using \<open>m \<le> n\<close>
proof (induction m)
  case (Suc m)
  moreover then have "n - m = Suc (n - Suc m)" by auto
  ultimately show ?case by (auto simp: inv)
qed simp




section \<open>Function-power distance between values\<close>

(* xxx move *)
definition funpow_dist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "funpow_dist f x y \<equiv> LEAST n. (f ^^ n) x = y"

abbreviation funpow_dist1 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "funpow_dist1 f x y \<equiv> Suc (funpow_dist f (f x) y)"

lemma funpow_dist_0:
  assumes "x = y" shows "funpow_dist f x y = 0"
  using assms unfolding funpow_dist_def by (intro Least_eq_0) simp

lemma funpow_dist_least:
  assumes "n < funpow_dist f x y" shows "(f ^^ n) x \<noteq> y"
proof (rule notI)
  assume "(f ^^ n) x = y"
  then have "funpow_dist f x y \<le> n" unfolding funpow_dist_def by (rule Least_le)
  with assms show False by linarith
qed

lemma funpow_dist1_least:
  assumes "0 < n" "n < funpow_dist1 f x y" shows "(f ^^ n) x \<noteq> y"
proof (rule notI)
  assume "(f ^^ n) x = y"
  then have "(f ^^ (n - 1)) (f x) = y"
    using \<open>0 < n\<close> by (cases n) (simp_all add: funpow_swap1)
  then have "funpow_dist f (f x) y \<le> n - 1" unfolding funpow_dist_def by (rule Least_le)
  with assms show False by simp
qed


section \<open>Cyclic Permutations\<close>

inductive_set orbit :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set" for f x where
  base: "f x \<in> orbit f x" |
  step: "y \<in> orbit f x \<Longrightarrow> f y \<in> orbit f x"

definition cyclic_on :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "cyclic_on f S \<longleftrightarrow> (\<exists>s\<in>S. S = orbit f s)"

lemma orbit_altdef: "orbit f x = {(f ^^ n) x | n. 0 < n}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix y assume "y \<in> ?L" then show "y \<in> ?R"
    by (induct rule: orbit.induct) (auto simp: exI[where x=1] exI[where x="Suc n" for n])
next
  fix y assume "y \<in> ?R"
  then obtain n where "y = (f ^^ n) x" "0 < n" by blast
  then show "y \<in> ?L"
  proof (induction n arbitrary: y)
    case (Suc n) then show ?case by (cases "n = 0") (auto intro: orbit.intros)
  qed simp
qed

lemma orbit_trans:
  assumes "s \<in> orbit f t" "t \<in> orbit f u" shows "s \<in> orbit f u"
  using assms by induct (auto intro: orbit.intros)

lemma orbit_subset:
  assumes "s \<in> orbit f (f t)" shows "s \<in> orbit f t"
  using assms by (induct) (auto intro: orbit.intros)

lemma orbit_sim_step:
  assumes "s \<in> orbit f t" shows "f s \<in> orbit f (f t)"
  using assms by induct (auto intro: orbit.intros)

lemma orbit_step:
  assumes "y \<in> orbit f x" "f x \<noteq> y" shows "y \<in> orbit f (f x)"
  using assms
proof induction
  case (step y) then show ?case by (cases "x = y") (auto intro: orbit.intros)
qed simp

lemma self_in_orbit_trans:
  assumes "s \<in> orbit f s" "t \<in> orbit f s" shows "t \<in> orbit f t"
  using assms(2,1) by induct (auto intro: orbit_sim_step)

lemma orbit_swap:
  assumes "s \<in> orbit f s" "t \<in> orbit f s" shows "s \<in> orbit f t"
  using assms(2,1)
proof induction
  case base then show ?case by (cases "f s = s") (auto intro: orbit_step)
next
  case (step x) then show ?case by (cases "f x = s") (auto intro: orbit_step)
qed

lemma permutation_self_in_orbit:
  assumes "permutation f" shows "s \<in> orbit f s"
  unfolding orbit_altdef using permutation_self[OF assms, of s] by simp metis

lemma orbit_altdef_self_in:
  assumes "s \<in> orbit f s" shows "orbit f s = {(f ^^ n) s | n. True}"
proof (intro set_eqI iffI)
  fix x assume "x \<in> {(f ^^ n) s | n. True}"
  then obtain n where "x = (f ^^ n) s" by auto
  then show "x \<in> orbit f s" using assms by (cases "n = 0") (auto simp: orbit_altdef)
qed (auto simp: orbit_altdef)

lemma orbit_altdef_permutation:
  assumes "permutation f" shows "orbit f s = {(f ^^ n) s | n. True}"
  using assms by (intro orbit_altdef_self_in permutation_self_in_orbit)

lemma orbit_altdef_bounded:
  assumes "(f ^^ n) s = s" "0 < n" shows "orbit f s = {(f ^^ m) s| m. m < n}"
proof -
  from assms have "s \<in> orbit f s" unfolding orbit_altdef by auto metis
  then have "orbit f s = {(f ^^ m) s|m. True}" by (rule orbit_altdef_self_in)
  also have "\<dots> = {(f ^^ m) s| m. m < n}"
    using assms by (auto simp: funpow_mod_eq intro: exI[where x="m mod n" for m])
  finally show ?thesis .
qed

lemma funpow_in_orbit:
  assumes "s \<in> orbit f t" shows "(f ^^ n) s \<in> orbit f t"
  using assms by (induct n) (auto intro: orbit.intros)

lemma finite_orbit:
  assumes "s \<in> orbit f s" shows "finite (orbit f s)"
proof -
  from assms obtain n where n: "0 < n" "(f ^^n) s = s" by (auto simp: orbit_altdef)
  then show ?thesis by (auto simp: orbit_altdef_bounded)
qed

lemma self_in_orbit_step:
  assumes "s \<in> orbit f s" shows "orbit f (f s) = orbit f s"
proof (intro set_eqI iffI)
  fix t assume "t \<in> orbit f s" then show "t \<in> orbit f (f s)"
    using assms by (auto intro: orbit_step orbit_sim_step)
qed (auto intro: orbit_subset)

lemma permutation_orbit_step:
  assumes "permutation f" shows "orbit f (f s) = orbit f s"
  using assms by (intro self_in_orbit_step permutation_self_in_orbit)

lemma orbit_nonempty:
  "orbit f s \<noteq> {}"
  using orbit.base by fastforce

lemma orbit_inv_eq:
  assumes "permutation f"
  shows "orbit (inv f) x = orbit f x" (is "?L = ?R")
proof -
  { fix g y assume A: "permutation g" "y \<in> orbit (inv g) x"
    have "y \<in> orbit g x"
    proof -
      have inv_g: "\<And>y. x = g y \<Longrightarrow> inv g x = y" "\<And>y. inv g (g y) = y"
        by (metis A(1) bij_inv_eq_iff permutation_bijective)+

      { fix y assume "y \<in> orbit g x"
        then have "inv g y \<in> orbit g x"
          by (cases) (simp_all add: inv_g A(1) permutation_self_in_orbit)
      } note inv_g_in_orb = this

      from A(2) show ?thesis
        by induct (simp_all add: inv_g_in_orb A permutation_self_in_orbit)
    qed
  } note orb_inv_ss = this

  have "inv (inv f) = f"
    by (simp add: assms inv_inv_eq permutation_bijective)
  then show ?thesis
    using orb_inv_ss[OF assms] orb_inv_ss[OF permutation_inverse[OF assms]] by auto
qed

lemma cyclic_on_alldef:
  "cyclic_on f S \<longleftrightarrow> S \<noteq> {} \<and> (\<forall>s\<in>S. S = orbit f s)"
  unfolding cyclic_on_def by (auto intro: orbit.step orbit_swap orbit_trans)


lemma cyclic_on_funpow_in:
  assumes "cyclic_on f S" "s \<in> S" shows "(f^^n) s \<in> S"
  using assms unfolding cyclic_on_def by (auto intro: funpow_in_orbit)

lemma finite_cyclic_on:
  assumes "cyclic_on f S" shows "finite S"
  using assms by (auto simp: cyclic_on_def finite_orbit)

lemma cyclic_on_singleI:
  assumes "s \<in> S" "S = orbit f s" shows "cyclic_on f S"
  using assms unfolding cyclic_on_def by blast

lemma inj_on_funpow_least:
  assumes "(f ^^ n) s = s" "\<And>m. \<lbrakk>m < n; 0 < m\<rbrakk> \<Longrightarrow> (f ^^ m) s \<noteq> s"
  shows "inj_on (\<lambda>k. (f^^k) s) {0..<n}"
proof -
  { fix k l assume A: "k < n" "l < n" "k \<noteq> l" "(f ^^ k) s = (f ^^ l) s"
    define k' l' where "k' = min k l" and "l' = max k l"
    with A have A': "k' < l'" "(f ^^ k') s = (f ^^ l') s" "l' < n"
      by (auto simp: min_def max_def)

    have "s = (f ^^ ((n - l') + l')) s" using assms \<open>l' < n\<close> by simp
    also have "\<dots> = (f ^^ (n - l')) ((f ^^ l') s)" by (simp add: funpow_add)
    also have "(f ^^ l') s = (f ^^ k') s" by (simp add: A')
    also have "(f ^^ (n - l')) \<dots> = (f ^^ (n - l' + k')) s" by (simp add: funpow_add)
    finally have "(f ^^ (n - l' + k')) s = s" by simp
    moreover have "n - l' + k' < n" "0 < n - l' + k'"using A' by linarith+
    ultimately have False using assms(2) by auto
  }
  then show ?thesis by (intro inj_onI) auto
qed

lemma cyclic_on_inI:
  assumes "cyclic_on f S" "s \<in> S" shows "f s \<in> S"
  using assms by (auto simp: cyclic_on_def intro: orbit.intros)

lemma bij_betw_funpow:
  assumes "bij_betw f S S" shows "bij_betw (f ^^ n) S S"
proof (induct n)
  case 0 then show ?case by (auto simp: id_def[symmetric])
next
  case (Suc n)
  then show ?case unfolding funpow.simps using assms by (rule bij_betw_trans)
qed

(*XXX rename move*)
lemma orbit_FOO:
  assumes self:"a \<in> orbit g a"
    and eq: "\<And>x. x \<in> orbit g a \<Longrightarrow>  g' (f x) = f (g x)"
  shows "f ` orbit g a = orbit g' (f a)" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix x assume "x \<in> ?L"
  then obtain x0 where "x0 \<in> orbit g a" "x = f x0" by auto
  then show "x \<in> ?R"
  proof (induct arbitrary: x)
    case base then show ?case by (auto simp: self orbit.base eq[symmetric])
  next
    case step then show ?case by cases (auto simp: eq[symmetric] orbit.intros)
  qed
next
  fix x assume "x \<in> ?R"
  then show "x \<in> ?L"
  proof (induct arbitrary: )
    case base then show ?case by (auto simp: self orbit.base eq)
  next
    case step then show ?case by cases (auto simp: eq orbit.intros)
  qed
qed

lemma cyclic_on_FOO:
  assumes "cyclic_on f S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> g (h x) = h (f x)"
  shows "cyclic_on g (h ` S)"
  using assms by (auto simp: cyclic_on_def) (meson orbit_FOO)

lemma cyclic_on_f_in:
  assumes "f permutes S" "cyclic_on f A" "f x \<in> A"
  shows "x \<in> A"
proof -
  from assms have fx_in_orb: "f x \<in> orbit f (f x)" by (auto simp: cyclic_on_alldef)
  from assms have "A = orbit f (f x)" by (auto simp: cyclic_on_alldef)
  moreover
  then have "\<dots> = orbit f x" using \<open>f x \<in> A\<close> by (auto intro: orbit_step orbit_subset)
  ultimately
    show ?thesis by (metis (no_types) orbit.simps permutes_inverses(2)[OF assms(1)])
qed

lemma permutes_not_in:
  assumes "f permutes S" "x \<notin> S" shows "f x = x"
  using assms by (auto simp: permutes_def)

lemma orbit_cong0:
  assumes "x \<in> A" "f \<in> A \<rightarrow> A" "\<And>y. y \<in> A \<Longrightarrow> f y = g y" shows "orbit f x = orbit g x"
proof -
  { fix n have "(f ^^ n) x = (g ^^ n) x \<and> (f ^^ n) x \<in> A"
      by (induct n rule: nat.induct) (insert assms, auto)
  } then show ?thesis by (auto simp: orbit_altdef)
qed

lemma orbit_cong:
  assumes self_in: "t \<in> orbit f t" and eq: "\<And>s. s \<in> orbit f t \<Longrightarrow> g s = f s"
  shows "orbit g t = orbit f t"
  using assms(1) _ assms(2) by (rule orbit_cong0) (auto simp: orbit.step eq)

lemma cyclic_cong:
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g s" shows "cyclic_on f S = cyclic_on g S"
proof -
  have "(\<exists>s\<in>S. orbit f s = orbit g s) \<Longrightarrow> cyclic_on f S = cyclic_on g S"
    by (metis cyclic_on_alldef cyclic_on_def)
  then show ?thesis by (metis assms orbit_cong cyclic_on_def)
qed

lemma permutes_comp_preserves_cyclic1:
  assumes "g permutes B" "cyclic_on f C"
  assumes "A \<inter> B = {}" "C \<subseteq> A"
  shows "cyclic_on (f o g) C"
proof -
  have *: "\<And>c. c \<in> C \<Longrightarrow> f (g c) = f c"
    using assms by (subst permutes_not_in[where f=g]) auto
  with assms(2) show ?thesis by (simp cong: cyclic_cong)
qed

lemma permutes_comp_preserves_cyclic2:
  assumes "f permutes A" "cyclic_on g C"
  assumes "A \<inter> B = {}" "C \<subseteq> B"
  shows "cyclic_on (f o g) C"
proof -
  obtain c where c: "c \<in> C" "C = orbit g c" "c \<in> orbit g c"
    using \<open>cyclic_on g C\<close> by (auto simp: cyclic_on_def)
  then have "\<And>c. c \<in> C \<Longrightarrow> f (g c) = g c"
    using assms c by (subst permutes_not_in[where f=f]) (auto intro: orbit.intros)
  with assms(2) show ?thesis by (simp cong: cyclic_cong)
qed


(*XXX merge with previous section?*)
subsection \<open>Orbits\<close>

lemma permutes_orbit_subset:
  assumes "f permutes S" "x \<in> S" shows "orbit f x \<subseteq> S"
proof
  fix y assume "y \<in> orbit f x"
  then show "y \<in> S" by induct (auto simp: permutes_in_image assms)
qed

lemma cyclic_on_orbit':
  assumes "permutation f" shows "cyclic_on f (orbit f x)"
  unfolding cyclic_on_alldef using orbit_nonempty[of f x]
  by (auto intro: assms orbit_swap orbit_trans permutation_self_in_orbit)

(* XXX remove? *)
lemma cyclic_on_orbit:
  assumes "f permutes S" "finite S" shows "cyclic_on f (orbit f x)"
  using assms by (intro cyclic_on_orbit') (auto simp: permutation_permutes)

lemma orbit_cyclic_eq3:
  assumes "cyclic_on f S" "y \<in> S" shows "orbit f y = S"
  using assms unfolding cyclic_on_alldef by simp

(*XXX move*)
lemma orbit_eq_singleton_iff: "orbit f x = {x} \<longleftrightarrow> f x = x" (is "?L \<longleftrightarrow> ?R")
proof
  assume A: ?R
  { fix y assume "y \<in> orbit f x" then have "y = x"
      by induct (auto simp: A)
  } then show ?L by (metis orbit_nonempty singletonI subsetI subset_singletonD)
next
  assume A: ?L
  then have "\<And>y. y \<in> orbit f x \<Longrightarrow> f x = y"
    by - (erule orbit.cases, simp_all)
  then show ?R using A by blast
qed

(* XXX move *)
lemma eq_on_cyclic_on_iff1:
  assumes "cyclic_on f S" "x \<in> S"
  obtains "f x \<in> S" "f x = x \<longleftrightarrow> card S = 1"
proof
  from assms show "f x \<in> S" by (auto simp: cyclic_on_def intro: orbit.intros)
  from assms have "S = orbit f x" by (auto simp: cyclic_on_alldef)
  then have "f x = x \<longleftrightarrow> S = {x}" by (metis orbit_eq_singleton_iff)
  then show "f x = x \<longleftrightarrow> card S = 1" using \<open>x \<in> S\<close> by (auto simp: card_Suc_eq)
qed







subsection \<open>Decomposition of Arbitrary Permutations\<close>

definition perm_restrict :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "perm_restrict f S x \<equiv> if x \<in> S then f x else x"

lemma perm_restrict_comp:
  assumes "A \<inter> B = {}" "cyclic_on f B"
  shows "perm_restrict f A o perm_restrict f B = perm_restrict f (A \<union> B)"
proof -
  have "\<And>x. x \<in> B \<Longrightarrow> f x \<in> B" using \<open>cyclic_on f B\<close> by (rule cyclic_on_inI)
  with assms show ?thesis by (auto simp: perm_restrict_def fun_eq_iff)
qed

lemma perm_restrict_simps:
  "x \<in> S \<Longrightarrow> perm_restrict f S x = f x"
  "x \<notin> S \<Longrightarrow> perm_restrict f S x = x"
  by (auto simp: perm_restrict_def)

lemma perm_restrict_perm_restrict:
  "perm_restrict (perm_restrict f A) B = perm_restrict f (A \<inter> B)"
  by (auto simp: perm_restrict_def)

lemma perm_restrict_union:
  assumes "perm_restrict f A permutes A" "perm_restrict f B permutes B" "A \<inter> B = {}"
  shows "perm_restrict f A o perm_restrict f B = perm_restrict f (A \<union> B)"
  using assms by (auto simp: fun_eq_iff perm_restrict_def permutes_def) (metis Diff_iff Diff_triv)

lemma perm_restrict_id[simp]:
  assumes "f permutes S" shows "perm_restrict f S = f"
  using assms by (auto simp: permutes_def perm_restrict_def)

lemma cyclic_on_perm_restrict:
  "cyclic_on (perm_restrict f S) S \<longleftrightarrow> cyclic_on f S"
  by (simp add: perm_restrict_def cong: cyclic_cong)

lemma perm_restrict_diff_cyclic:
  assumes "f permutes S" "cyclic_on f A"
  shows "perm_restrict f (S - A) permutes (S - A)"
proof -
  { fix y
    have "\<exists>x. perm_restrict f (S - A) x = y"
    proof cases
      assume A: "y \<in> S - A"
      with \<open>f permutes S\<close> obtain x where "f x = y" "x \<in> S"
        unfolding permutes_def by auto metis
      moreover
      with A have "x \<notin> A" by (metis Diff_iff assms(2) cyclic_on_inI)
      ultimately
      have "perm_restrict f (S - A) x = y"  by (simp add: perm_restrict_simps)
      then show ?thesis ..
    next
      assume "y \<notin> S - A"
      then have "perm_restrict f (S - A) y = y" by (simp add: perm_restrict_simps)
      then show ?thesis ..
    qed
  } note X = this

  { fix x y assume "perm_restrict f (S - A) x = perm_restrict f (S - A) y"
    with assms have "x = y"
      by (auto simp: perm_restrict_def permutes_def split: if_splits intro: cyclic_on_f_in)
  } note Y = this

  show ?thesis by (auto simp: permutes_def perm_restrict_simps X intro: Y)
qed

lemma orbit_eqI:
  "y = f x \<Longrightarrow> y \<in> orbit f x"
  "z = f y \<Longrightarrow>y \<in> orbit f x \<Longrightarrow>z \<in> orbit f x"
  by (metis orbit.base) (metis orbit.step)

lemma permutes_decompose:
  assumes "f permutes S" "finite S"
  shows "\<exists>C. (\<forall>c \<in> C. cyclic_on f c) \<and> \<Union>C = S \<and> (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {})"
  using assms(2,1)
proof (induction arbitrary: f rule: finite_psubset_induct)
  case (psubset S)

  show ?case
  proof (cases "S = {}")
    case True then show ?thesis by (intro exI[where x="{}"]) auto
  next
    case False
    then obtain s where "s \<in> S" by auto
    with \<open>f permutes S\<close> have "orbit f s \<subseteq> S"
      by (rule permutes_orbit_subset)
    have cyclic_orbit: "cyclic_on f (orbit f s)"
      using \<open>f permutes S\<close> \<open>finite S\<close> by (rule cyclic_on_orbit)

    let ?f' = "perm_restrict f (S - orbit f s)"

    have "f s \<in> S" using \<open>f permutes S\<close> \<open>s \<in> S\<close> by (auto simp: permutes_in_image)
    then have "S - orbit f s \<subset> S" using orbit.base[of f s] \<open>s \<in> S\<close> by blast
    moreover
    have "?f' permutes (S - orbit f s)"
      using \<open>f permutes S\<close> cyclic_orbit by (rule perm_restrict_diff_cyclic)
    ultimately
    obtain C where C: "\<And>c. c \<in> C \<Longrightarrow> cyclic_on ?f' c" "\<Union>C = S - orbit f s"
        "\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}"
      using psubset.IH by metis

    { fix c assume "c \<in> C"
      then have *: "\<And>x. x \<in> c \<Longrightarrow> perm_restrict f (S - orbit f s) x = f x"
        using C(2) \<open>f permutes S\<close> by (auto simp add: perm_restrict_def)
      then have "cyclic_on f c" using C(1)[OF \<open>c \<in> C\<close>] by (simp cong: cyclic_cong add: *)
    } note in_C_cyclic = this

    have Un_ins: "\<Union>(insert (orbit f s) C) = S"
      using \<open>\<Union>C = _\<close>  \<open>orbit f s \<subseteq> S\<close> by blast

    have Disj_ins: "(\<forall>c1 \<in> insert (orbit f s) C. \<forall>c2 \<in> insert (orbit f s) C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {})"
      using C by auto

    show ?thesis
      by (intro conjI Un_ins Disj_ins exI[where x="insert (orbit f s) C"])
        (auto simp: cyclic_orbit in_C_cyclic)
  qed
qed


subsection \<open>Funpow + Orbit\<close>

lemma funpow_dist_prop:
  "y \<in> orbit f x \<Longrightarrow> (f ^^ funpow_dist f x y) x = y"
  unfolding funpow_dist_def by (rule LeastI_ex) (auto simp: orbit_altdef)

lemma funpow_dist_0_eq:
  assumes "y \<in> orbit f x" shows "funpow_dist f x y = 0 \<longleftrightarrow> x = y"
  using assms by (auto simp: funpow_dist_0 dest: funpow_dist_prop)

lemma funpow_dist_step:
  assumes "x \<noteq> y" "y \<in> orbit f x" shows "funpow_dist f x y = Suc (funpow_dist f (f x) y)"
proof -
  from \<open>y \<in> _\<close> obtain n where "(f ^^ n) x = y" by (auto simp: orbit_altdef)
  with \<open>x \<noteq> y\<close> obtain n' where [simp]: "n = Suc n'" by (cases n) auto

  show ?thesis
    unfolding funpow_dist_def
  proof (rule Least_Suc2)
    show "(f ^^ n) x = y" by fact
    then show "(f ^^ n') (f x) = y" by (simp add: funpow_swap1)
    show "(f ^^ 0) x \<noteq> y" using \<open>x \<noteq> y\<close> by simp
    show "\<forall>k. ((f ^^ Suc k) x = y) = ((f ^^ k) (f x) = y)"
      by (simp add: funpow_swap1)
  qed
qed

lemma funpow_dist1_prop:
  assumes "y \<in> orbit f x" shows "(f ^^ funpow_dist1 f x y) x = y"
  by (metis assms funpow.simps(1) funpow_dist_0 funpow_dist_prop funpow_simp_l funpow_swap1 id_apply orbit_step)

(*XXX simplify? *)
lemma funpow_neq_less_funpow_dist:
  assumes "y \<in> orbit f x" "m \<le> funpow_dist f x y" "n \<le> funpow_dist f x y" "m \<noteq> n"
  shows "(f ^^ m) x \<noteq> (f ^^ n) x"
proof (rule notI)
  assume A: "(f ^^ m) x = (f ^^ n) x"

  define m' n' where "m' = min m n" and "n' = max m n"
  with A assms have A': "m' < n'" "(f ^^ m') x = (f ^^ n') x" "n' \<le> funpow_dist f x y"
    by (auto simp: min_def max_def)

  have "y = (f ^^ funpow_dist f x y) x"
    using \<open>y \<in> _\<close> by (simp only: funpow_dist_prop)
  also have "\<dots> = (f ^^ ((funpow_dist f x y - n') + n')) x"
    using \<open>n' \<le> _\<close> by simp
  also have "\<dots> = (f ^^ ((funpow_dist f x y - n') + m')) x"
    by (simp add: funpow_add \<open>(f ^^ m') x = _\<close>)
  also have "(f ^^ ((funpow_dist f x y - n') + m')) x \<noteq> y"
    using A' by (intro funpow_dist_least) linarith
  finally show "False" by simp
qed

(* XXX reduce to funpow_neq_less_funpow_dist? *)
lemma funpow_neq_less_funpow_dist1:
  assumes "y \<in> orbit f x" "m < funpow_dist1 f x y" "n < funpow_dist1 f x y" "m \<noteq> n"
  shows "(f ^^ m) x \<noteq> (f ^^ n) x"
proof (rule notI)
  assume A: "(f ^^ m) x = (f ^^ n) x"

  define m' n' where "m' = min m n" and "n' = max m n"
  with A assms have A': "m' < n'" "(f ^^ m') x = (f ^^ n') x" "n' < funpow_dist1 f x y"
    by (auto simp: min_def max_def)

  have "y = (f ^^ funpow_dist1 f x y) x"
    using \<open>y \<in> _\<close> by (simp only: funpow_dist1_prop)
  also have "\<dots> = (f ^^ ((funpow_dist1 f x y - n') + n')) x"
    using \<open>n' < _\<close> by simp
  also have "\<dots> = (f ^^ ((funpow_dist1 f x y - n') + m')) x"
    by (simp add: funpow_add \<open>(f ^^ m') x = _\<close>)
  also have "(f ^^ ((funpow_dist1 f x y - n') + m')) x \<noteq> y"
    using A' by (intro funpow_dist1_least) linarith+
  finally show "False" by simp
qed

lemma inj_on_funpow_dist:
  assumes "y \<in> orbit f x" shows "inj_on (\<lambda>n. (f ^^ n) x) {0..funpow_dist f x y}"
  using funpow_neq_less_funpow_dist[OF assms] by (intro inj_onI) auto

lemma inj_on_funpow_dist1:
  assumes "y \<in> orbit f x" shows "inj_on (\<lambda>n. (f ^^ n) x) {0..<funpow_dist1 f x y}"
  using funpow_neq_less_funpow_dist1[OF assms] by (intro inj_onI) auto

lemma orbit_conv_funpow_dist1:
  assumes "x \<in> orbit f x"
  shows "orbit f x = (\<lambda>n. (f ^^ n) x) ` {0..<funpow_dist1 f x x}" (is "?L = ?R")
  using funpow_dist1_prop[OF assms]
  by (auto simp: orbit_altdef_bounded[where n="funpow_dist1 f x x"])

lemma funpow_dist1_prop1:
  assumes "(f ^^ n) x = y" "0 < n" shows "(f ^^ funpow_dist1 f x y) x = y"
proof -
  from assms have "y \<in> orbit f x" by (auto simp: orbit_altdef)
  then show ?thesis by (rule funpow_dist1_prop)
qed

lemma funpow_dist1_dist:
  assumes "funpow_dist1 f x y < funpow_dist1 f x z"
  assumes "{y,z} \<subseteq> orbit f x"
  shows "funpow_dist1 f x z = funpow_dist1 f x y + funpow_dist1 f y z" (is "?L = ?R")
proof -
  have x_z: "(f ^^ funpow_dist1 f x z) x = z" using assms by (blast intro: funpow_dist1_prop)
  have x_y: "(f ^^ funpow_dist1 f x y) x = y" using assms by (blast intro: funpow_dist1_prop)

  have "(f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) y
      = (f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) ((f ^^ funpow_dist1 f x y) x)"
    using x_y by simp
  also have "\<dots> = z"
    using assms x_z by (simp del: funpow.simps add: funpow_add_app)
  finally have y_z_diff: "(f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) y = z" .
  then have "(f ^^ funpow_dist1 f y z) y = z"
    using assms by (intro funpow_dist1_prop1) auto
  then have "(f ^^ funpow_dist1 f y z) ((f ^^ funpow_dist1 f x y) x) = z"
    using x_y by simp
  then have "(f ^^ (funpow_dist1 f y z + funpow_dist1 f x y)) x = z"
    by (simp del: funpow.simps add: funpow_add_app)

  show ?thesis
  proof (rule antisym)
    from y_z_diff have "(f ^^ funpow_dist1 f y z) y = z"
      using assms by (intro funpow_dist1_prop1) auto
    then have "(f ^^ funpow_dist1 f y z) ((f ^^ funpow_dist1 f x y) x) = z"
      using x_y by simp
    then have "(f ^^ (funpow_dist1 f y z + funpow_dist1 f x y)) x = z"
      by (simp del: funpow.simps add: funpow_add_app)
    then have "funpow_dist1 f x z \<le> funpow_dist1 f y z + funpow_dist1 f x y"
      using funpow_dist1_least not_less by fastforce
    then show "?L \<le> ?R" by presburger
  next
    have "funpow_dist1 f y z \<le> funpow_dist1 f x z - funpow_dist1 f x y"
      using y_z_diff assms(1) by (metis not_less zero_less_diff funpow_dist1_least)
    then show "?R \<le> ?L" by linarith
  qed
qed

lemma funpow_dist1_le_self:
  assumes "(f ^^ m) x = x" "0 < m" "y \<in> orbit f x"
  shows "funpow_dist1 f x y \<le> m"
proof (cases "x = y")
  case True with assms show ?thesis by (auto dest!: funpow_dist1_least)
next
  case False
  have "(f ^^ funpow_dist1 f x y) x = (f ^^ (funpow_dist1 f x y mod m)) x"
    using assms by (simp add: funpow_mod_eq)
  with False \<open>y \<in> orbit f x\<close> have "funpow_dist1 f x y \<le> funpow_dist1 f x y mod m"
    by auto (metis funpow_dist_least funpow_dist_prop funpow_dist_step funpow_simp_l not_less) 
  with \<open>m > 0\<close> show ?thesis
    by (auto intro: order_trans)
qed


subsection \<open>Permutation Domains\<close>

definition has_dom :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "has_dom f S \<equiv> \<forall>s. s \<notin> S \<longrightarrow> f s = s"

lemma permutes_conv_has_dom:
  "f permutes S \<longleftrightarrow> bij f \<and> has_dom f S"
  by (auto simp: permutes_def has_dom_def bij_iff)



section \<open>Segments\<close>

inductive_set segment :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" for f a b where
  base: "f a \<noteq> b \<Longrightarrow> f a \<in> segment f a b" |
  step: "x \<in> segment f a b \<Longrightarrow> f x \<noteq> b \<Longrightarrow> f x \<in> segment f a b"

lemma segment_step_2D:
  assumes "x \<in> segment f a (f b)" shows "x \<in> segment f a b \<or> x = b"
  using assms by induct (auto intro: segment.intros)

lemma not_in_segment2D:
  assumes "x \<in> segment f a b" shows "x \<noteq> b"
  using assms by induct auto

lemma segment_altdef:
  assumes "b \<in> orbit f a"
  shows "segment f a b = (\<lambda>n. (f ^^ n) a) ` {1..<funpow_dist1 f a b}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix x assume "x \<in> ?L"
  have "f a \<noteq>b \<Longrightarrow> b \<in> orbit f (f a)"
    using assms  by (simp add: orbit_step)
  then have *: "f a \<noteq> b \<Longrightarrow> 0 < funpow_dist f (f a) b"
    using assms using gr0I funpow_dist_0_eq[OF \<open>_ \<Longrightarrow> b \<in> orbit f (f a)\<close>] by (simp add: orbit.intros)
  from \<open>x \<in> ?L\<close> show "x \<in> ?R"
  proof induct
    case base then show ?case by (intro image_eqI[where x=1]) (auto simp: *)
  next
    case step then show ?case using assms funpow_dist1_prop less_antisym
      by (fastforce intro!: image_eqI[where x="Suc n" for n])
  qed
next
  fix x assume "x \<in> ?R"
  then obtain n where "(f ^^ n ) a = x" "0 < n" "n < funpow_dist1 f a b" by auto
  then show "x \<in> ?L"
  proof (induct n arbitrary: x)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "(f ^^ Suc n) a \<noteq> b" using Suc by (meson funpow_dist1_least)
    with Suc show ?case by (cases "n = 0") (auto intro: segment.intros)
  qed
qed

(*XXX move up*)
lemma segmentD_orbit:
  assumes "x \<in> segment f y z" shows "x \<in> orbit f y"
  using assms by induct (auto intro: orbit.intros)

lemma segment1_empty: "segment f x (f x) = {}"
  by (auto simp: segment_altdef orbit.base funpow_dist_0)

lemma segment_subset:
  assumes "y \<in> segment f x z"
  assumes "w \<in> segment f x y"
  shows "w \<in> segment f x z"
  using assms by (induct arbitrary: w) (auto simp: segment1_empty intro: segment.intros dest: segment_step_2D elim: segment.cases)

(* XXX move up*)
lemma not_in_segment1:
  assumes "y \<in> orbit f x" shows "x \<notin> segment f x y"
proof
  assume "x \<in> segment f x y"
  then obtain n where n: "0 < n" "n < funpow_dist1 f x y" "(f ^^ n) x = x"
    using assms by (auto simp: segment_altdef Suc_le_eq)
  then have neq_y: "(f ^^ (funpow_dist1 f x y - n)) x \<noteq> y" by (simp add: funpow_dist1_least)

  have "(f ^^ (funpow_dist1 f x y - n)) x = (f ^^ (funpow_dist1 f x y - n)) ((f ^^ n) x)"
    using n by (simp add: funpow_add_app)
  also have "\<dots> = (f ^^ funpow_dist1 f x y) x"
    using \<open>n < _\<close> by (simp add: funpow_add_app)
  also have "\<dots> = y" using assms by (rule funpow_dist1_prop)
  finally show False using neq_y by contradiction
qed

lemma not_in_segment2: "y \<notin> segment f x y"
  using not_in_segment2D by metis

(*XXX move*)
lemma in_segmentE:
  assumes "y \<in> segment f x z" "z \<in> orbit f x"
  obtains "(f ^^ funpow_dist1 f x y) x = y" "funpow_dist1 f x y < funpow_dist1 f x z"
proof
  from assms show "(f ^^ funpow_dist1 f x y) x = y"
    by (intro segmentD_orbit funpow_dist1_prop)
  moreover
  obtain n where "(f ^^ n) x = y" "0 < n" "n < funpow_dist1 f x z"
    using assms by (auto simp: segment_altdef)
  moreover then have "funpow_dist1 f x y \<le> n" by (meson funpow_dist1_least not_less)
  ultimately show "funpow_dist1 f x y < funpow_dist1 f x z" by linarith
qed

(*XXX move*)
lemma cyclic_split_segment:
  assumes S: "cyclic_on f S" "a \<in> S" "b \<in> S" and "a \<noteq> b"
  shows "S = {a,b} \<union> segment f a b \<union> segment f b a" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix c assume "c \<in> ?L"
  with S have "c \<in> orbit f a" unfolding cyclic_on_alldef by auto
  then show "c \<in> ?R" by induct (auto intro: segment.intros)
next
  fix c assume "c \<in> ?R"
  moreover have "segment f a b \<subseteq> orbit f a" "segment f b a \<subseteq> orbit f b"
    by (auto dest: segmentD_orbit)
  ultimately show "c \<in> ?L" using S by (auto simp: cyclic_on_alldef)
qed

(*XXX move*)
lemma segment_split:
  assumes y_in_seg: "y \<in> segment f x z"
  shows "segment f x z = segment f x y \<union> {y} \<union> segment f y z" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix w assume "w \<in> ?L" then show "w \<in> ?R" by induct (auto intro: segment.intros)
next
  fix w assume "w \<in> ?R"
  moreover
  { assume "w \<in> segment f x y" then have "w \<in> segment f x z"
    using segment_subset[OF y_in_seg] by auto }
  moreover
  { assume "w \<in> segment f y z" then have "w \<in> segment f x z"
      using y_in_seg by induct (auto intro: segment.intros) }
  ultimately
  show "w \<in> ?L" using y_in_seg by (auto intro: segment.intros)
qed

lemma in_segmentD_inv:
  assumes "x \<in> segment f a b" "x \<noteq> f a"
  assumes "inj f"
  shows "inv f x \<in> segment f a b"
  using assms by (auto elim: segment.cases)

lemma in_orbit_invI:
  assumes "b \<in> orbit f a"
  assumes "inj f"
  shows "a \<in> orbit (inv f) b"
  using assms(1)
  apply induct
   apply (simp add: assms(2) orbit_eqI(1))
  by (metis assms(2) inv_f_f orbit.base orbit_trans)

lemma segment_step_2:
  assumes A: "x \<in> segment f a b" "b \<noteq> a" and "inj f"
  shows "x \<in> segment f a (f b)"
  using A by induct (auto intro: segment.intros dest: not_in_segment2D injD[OF \<open>inj f\<close>])

lemma inv_end_in_segment:
  assumes "b \<in> orbit f a" "f a \<noteq> b" "bij f"
  shows "inv f b \<in> segment f a b"
  using assms(1,2)
proof induct
  case base then show ?case by simp
next
  case (step x)
  moreover
  from \<open>bij f\<close> have "inj f" by (rule bij_is_inj)
  moreover
  then have "x \<noteq> f x \<Longrightarrow> f a = x \<Longrightarrow> x \<in> segment f a (f x)" by (meson segment.simps)
  moreover
  have "x \<noteq> f x"
    using step \<open>inj f\<close> by (metis in_orbit_invI inv_f_eq not_in_segment1 segment.base)
  then have "inv f x \<in> segment f a (f x) \<Longrightarrow> x \<in> segment f a (f x)"
    using \<open>bij f\<close> \<open>inj f\<close> by (auto dest: segment.step simp: surj_f_inv_f bij_is_surj)
  then have "inv f x \<in> segment f a x \<Longrightarrow> x \<in> segment f a (f x)"
    using \<open>f a \<noteq> f x\<close> \<open>inj f\<close> by (auto dest: segment_step_2 injD)
  ultimately show ?case by (cases "f a = x") simp_all
qed

lemma segment_overlapping:
  assumes "x \<in> orbit f a" "x \<in> orbit f b" "bij f"
  shows "segment f a x \<subseteq> segment f b x \<or> segment f b x \<subseteq> segment f a x"
  using assms(1,2)
proof induction
  case base then show ?case by (simp add: segment1_empty)
next
  case (step x)
  from \<open>bij f\<close> have "inj f" by (simp add: bij_is_inj)
  have *: "\<And>f x y. y \<in> segment f x (f x) \<Longrightarrow> False" by (simp add: segment1_empty)
  { fix y z
    assume A: "y \<in> segment f b (f x)" "y \<notin> segment f a (f x)" "z \<in> segment f a (f x)"
    from \<open>x \<in> orbit f a\<close> \<open>f x \<in> orbit f b\<close> \<open>y \<in> segment f b (f x)\<close>
    have "x \<in> orbit f b"
      by (metis * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq[OF \<open>inj f\<close>] segmentD_orbit)
    moreover
    with \<open>x \<in> orbit f a\<close> step.IH
    have "segment f a (f x) \<subseteq> segment f b (f x) \<or> segment f b (f x) \<subseteq> segment f a (f x)"
      apply auto
       apply (metis * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq[OF \<open>inj f\<close>] segment_step_2D segment_subset step.prems subsetCE)
      by (metis (no_types, lifting) \<open>inj f\<close> * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq orbit_eqI(2) segment_step_2D segment_subset subsetCE)
    ultimately
    have "segment f a (f x) \<subseteq> segment f b (f x)" using A by auto
  } note C = this
  then show ?case by auto
qed

lemma segment_disj:
  assumes "a \<noteq> b" "bij f"
  shows "segment f a b \<inter> segment f b a = {}"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain x where x: "x \<in> segment f a b" "x \<in> segment f b a" by blast
  then have "segment f a b = segment f a x \<union> {x} \<union> segment f x b"
      "segment f b a = segment f b x \<union> {x} \<union> segment f x a"
    by (auto dest: segment_split)
  then have o: "x \<in> orbit f a" "x \<in> orbit f b" by (auto dest: segmentD_orbit)

  note * = segment_overlapping[OF o \<open>bij f\<close>]
  have "inj f" using \<open>bij f\<close> by (simp add: bij_is_inj)

  have "segment f a x = segment f b x"
  proof (intro set_eqI iffI)
    fix y assume A: "y \<in> segment f b x"
    then have "y \<in> segment f a x \<or> f a \<in> segment f b a"
      using * x(2) by (auto intro: segment.base segment_subset)
    then show "y \<in> segment f a x"
      using \<open>inj f\<close> A by (metis (no_types) not_in_segment2 segment_step_2)
  next
    fix y assume A: "y \<in> segment f a x "
    then have "y \<in> segment f b x \<or> f b \<in> segment f a b"
      using * x(1) by (auto intro: segment.base segment_subset)
    then show "y \<in> segment f b x"
      using \<open>inj f\<close> A by (metis (no_types) not_in_segment2 segment_step_2)
  qed
  moreover
  have "segment f a x \<noteq> segment f b x"
    by (metis assms bij_is_inj not_in_segment2 segment.base segment_step_2 segment_subset x(1))
  ultimately show False by contradiction
qed

lemma segment_x_x_eq:
  assumes "permutation f"
  shows "segment f x x = orbit f x - {x}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix y assume "y \<in> ?L" then show "y \<in> ?R" by (auto dest: segmentD_orbit simp: not_in_segment2)
next
  fix y assume "y \<in> ?R"
  then have "y \<in> orbit f x" "y \<noteq> x" by auto
  then show "y \<in> ?L" by induct (auto intro: segment.intros)
qed



section \<open>Lists of Powers\<close>

definition iterate :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a ) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "iterate m n f x = map (\<lambda>n. (f^^n) x) [m..<n]"

lemma set_iterate:
  "set (iterate m n f x) = (\<lambda>k. (f ^^ k) x) ` {m..<n} "
  by (auto simp: iterate_def)

lemma iterate_empty[simp]: "iterate n m f x = [] \<longleftrightarrow> m \<le> n"
  by (auto simp: iterate_def)

lemma iterate_length[simp]:
  "length (iterate m n f x) = n - m"
  by (auto simp: iterate_def)

lemma iterate_nth[simp]:
  assumes "k < n - m" shows "iterate m n f x ! k = (f^^(m+k)) x"
  using assms
  by (induct k arbitrary: m) (auto simp: iterate_def)

lemma iterate_applied:
  "iterate n m f (f x) = iterate (Suc n) (Suc m) f x"
  by (induct m arbitrary: n) (auto simp: iterate_def funpow_swap1)

end
