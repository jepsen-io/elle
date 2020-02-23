(* Title:  Stuff.thy
   Author: Lars Noschinski, TU München
*)

theory Stuff
imports
  Main
  "HOL-Library.Extended_Real"

begin

section \<open>Additional theorems for base libraries\<close>

text \<open>
  This section contains lemmas unrelated to graph theory which might be
  interesting for the Isabelle distribution
\<close>

lemma ereal_Inf_finite_Min:
  fixes S :: "ereal set"
  assumes "finite S" and "S \<noteq> {}"
  shows "Inf S = Min S"
using assms
by (induct S rule: finite_ne_induct) (auto simp: min_absorb1)

lemma finite_INF_in:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "finite S"
  assumes "S \<noteq> {}"
  shows "(INF s\<in> S. f s) \<in> f ` S"
proof -
  from assms
  have "finite (f ` S)" "f ` S \<noteq> {}" by auto
  then show "Inf (f ` S) \<in> f ` S"
    using ereal_Inf_finite_Min [of "f ` S"]  by simp
qed

lemma not_mem_less_INF:
  fixes f :: "'a \<Rightarrow> 'b :: complete_lattice"
  assumes "f x < (INF s\<in> S. f s)"
  assumes "x \<in> S"
  shows "False"
using assms by (metis INF_lower less_le_not_le)

lemma sym_diff:
  assumes "sym A" "sym B" shows "sym (A - B)"
using assms by (auto simp: sym_def)



subsection \<open>List\<close>

lemmas list_exhaust2 = list.exhaust[case_product list.exhaust]

lemma list_exhaust_NSC:
  obtains (Nil) "xs = []" | (Single) x where "xs = [x]" | (Cons_Cons) x y ys where "xs = x # y # ys"
by (metis list.exhaust)

lemma tl_rev:
  "tl (rev p) = rev (butlast p)"
by (induct p) auto

lemma butlast_rev:
  "butlast (rev p) = rev (tl p)"
by (induct p) auto

lemma take_drop_take:
   "take n xs @ drop n (take m xs) = take (max n m) xs"
proof cases
  assume "m < n" then show ?thesis by (auto simp: max_def)
next
  assume "\<not>m < n"
  then have "take n xs = take n (take m xs)" by (auto simp: min_def)
  then show ?thesis by (simp del: take_take add: max_def)
qed

lemma drop_take_drop:
  "drop n (take m xs) @ drop m xs = drop (min n m) xs"
proof cases
  assume A: "\<not>m < n"
  then show ?thesis
    using drop_append[of n "take m xs" "drop m xs"]
  by (cases "length xs < n") (auto simp: not_less min_def)
qed (auto simp: min_def)

lemma not_distinct_decomp_min_prefix:
  assumes "\<not> distinct ws"
  shows "\<exists> xs ys zs y. ws = xs @ y # ys @ y # zs \<and> distinct xs \<and> y \<notin> set xs \<and> y \<notin> set ys "
proof -
  obtain xs y ys where "y \<in> set xs" "distinct xs" "ws = xs @ y # ys"
    using assms by (auto simp: not_distinct_conv_prefix)
  moreover then obtain xs' ys' where "xs = xs' @ y # ys'" by (auto simp: in_set_conv_decomp)
  ultimately show ?thesis by auto
qed

lemma not_distinct_decomp_min_not_distinct:
  assumes "\<not> distinct ws"
  shows "\<exists>xs y ys zs. ws = xs @ y # ys @ y # zs \<and> distinct (ys @ [y])"
using assms
proof (induct ws)
  case (Cons w ws)
  show ?case
  proof (cases "distinct ws")
    case True
    then obtain xs ys where "ws = xs @ w # ys" "w \<notin> set xs"
      using Cons.prems by (fastforce dest: split_list_first)
    then have "distinct (xs @ [w])" "w # ws = [] @ w # xs @ w # ys"
      using \<open>distinct ws\<close> by auto
    then show ?thesis by blast
  next
    case False
    then obtain xs y ys zs where "ws = xs @ y # ys @ y # zs \<and> distinct (ys @ [y])"
      using Cons by auto
    then have "w # ws = (w # xs) @ y # ys @ y # zs \<and> distinct (ys @ [y])"
      by simp
    then show ?thesis by blast
  qed
qed simp

lemma card_Ex_subset:
  "k \<le> card M \<Longrightarrow> \<exists>N. N \<subseteq> M \<and> card N = k"
by (induct rule: inc_induct) (auto simp: card_Suc_eq)

lemma list_set_tl: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
by (cases xs) auto


section \<open>NOMATCH simproc\<close>

text \<open>
 The simplification procedure can be used to avoid simplification of terms of a certain form
\<close>

definition NOMATCH :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "NOMATCH val pat \<equiv> True"
lemma NOMATCH_cong[cong]: "NOMATCH val pat = NOMATCH val pat" by (rule refl)

simproc_setup NOMATCH ("NOMATCH val pat") = \<open>fn _ => fn ctxt => fn ct =>
  let
    val thy = Proof_Context.theory_of ctxt
    val dest_binop = Term.dest_comb #> apfst (Term.dest_comb #> snd)
    val m = Pattern.matches thy (dest_binop (Thm.term_of ct))
  in if m then NONE else SOME @{thm NOMATCH_def} end
\<close>

text \<open>
  This setup ensures that a rewrite rule of the form @{term "NOMATCH val pat \<Longrightarrow> t"}
  is only applied, if the pattern @{term pat} does not match the value @{term val}.
\<close>


end
