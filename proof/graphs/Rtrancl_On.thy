(* Title:  Rtrancl_On.thy
   Author: Lars Noschinski, TU München
   Author: René Neumann, TU München
*)

theory Rtrancl_On
imports Main
begin

section \<open>Reflexive-Transitive Closure on a Domain\<close>

text \<open>
  In this section we introduce a variant of the reflexive-transitive closure
  of a relation which is useful to formalize the reachability relation on
  digraphs.
\<close>

inductive_set
  rtrancl_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel"
  for F :: "'a set" and r :: "'a rel"
where
    rtrancl_on_refl [intro!, Pure.intro!, simp]: "a \<in> F \<Longrightarrow> (a, a) \<in> rtrancl_on F r"
  | rtrancl_on_into_rtrancl_on [Pure.intro]:
      "(a, b) \<in> rtrancl_on F r  \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> c \<in> F
      \<Longrightarrow> (a, c) \<in> rtrancl_on F r"

definition symcl :: "'a rel \<Rightarrow> 'a rel" ("(_\<^sup>s)" [1000] 999) where
  "symcl R = R \<union> (\<lambda>(a,b). (b,a)) ` R"

lemma in_rtrancl_on_in_F:
  assumes "(a,b) \<in> rtrancl_on F r" shows "a \<in> F" "b \<in> F"
  using assms by induct auto

lemma rtrancl_on_induct[consumes 1, case_names base step, induct set: rtrancl_on]:
  assumes "(a, b) \<in> rtrancl_on F r"
    and "a \<in> F \<Longrightarrow> P a"
        "\<And>y z. \<lbrakk>(a, y) \<in> rtrancl_on F r; (y,z) \<in> r; y \<in> F; z \<in> F; P y\<rbrakk> \<Longrightarrow> P z"
  shows "P b"
  using assms by (induct a b) (auto dest: in_rtrancl_on_in_F)

lemma rtrancl_on_trans:
  assumes "(a,b) \<in> rtrancl_on F r" "(b,c) \<in> rtrancl_on F r" shows "(a,c) \<in> rtrancl_on F r"
  using assms(2,1)
  by induct (auto intro: rtrancl_on_into_rtrancl_on)

lemma converse_rtrancl_on_into_rtrancl_on:
  assumes "(a,b) \<in> r" "(b, c) \<in> rtrancl_on F r" "a \<in> F"
  shows "(a, c) \<in> rtrancl_on F r"
proof -
  have "b \<in> F" using \<open>(b,c) \<in> _\<close> by (rule in_rtrancl_on_in_F)
  show ?thesis
    apply (rule rtrancl_on_trans)
    apply (rule rtrancl_on_into_rtrancl_on)
    apply (rule rtrancl_on_refl)
    by fact+
qed

lemma rtrancl_on_converseI:
  assumes "(y, x) \<in> rtrancl_on F r" shows "(x, y) \<in> rtrancl_on F (r\<inverse>)"
  using assms
proof induct
  case (step a b)
  then have "(b,b) \<in> rtrancl_on F (r\<inverse>)" "(b,a) \<in> r\<inverse>" by auto
  then show ?case using step
    by (metis rtrancl_on_trans rtrancl_on_into_rtrancl_on)
qed auto

theorem rtrancl_on_converseD:
  assumes "(y, x) \<in> rtrancl_on F (r\<inverse>)" shows "(x, y) \<in> rtrancl_on F r"
  using assms by - (drule rtrancl_on_converseI, simp)

lemma converse_rtrancl_on_induct[consumes 1, case_names base step, induct set: rtrancl_on]:
  assumes major: "(a, b) \<in> rtrancl_on F r"
    and cases: "b \<in> F \<Longrightarrow> P b"
       "\<And>x y. \<lbrakk>(x,y) \<in> r; (y,b) \<in> rtrancl_on F r; x \<in> F; y \<in> F; P y\<rbrakk> \<Longrightarrow> P x"
  shows "P a"
  using rtrancl_on_converseI[OF major] cases
  by induct (auto intro: rtrancl_on_converseD)

lemma converse_rtrancl_on_cases:
  assumes "(a, b) \<in> rtrancl_on F r"
  obtains (base) "a = b" "b \<in> F"
    | (step) c where "(a,c) \<in> r" "(c,b) \<in> rtrancl_on F r"
  using assms by induct auto

lemma rtrancl_on_sym:
  assumes "sym r" shows "sym (rtrancl_on F r)"
using assms by (auto simp: sym_conv_converse_eq intro: symI dest: rtrancl_on_converseI)

lemma rtrancl_on_mono:
  assumes "s \<subseteq> r" "F \<subseteq> G" "(a,b) \<in> rtrancl_on F s" shows "(a,b) \<in> rtrancl_on G r"
  using assms(3,1,2)
proof induct
  case (step x y) show ?case
    using step assms by (intro converse_rtrancl_on_into_rtrancl_on[OF _ step(5)]) auto
qed auto

lemma rtrancl_consistent_rtrancl_on:
  assumes "(a,b) \<in> r\<^sup>*"
  and "a \<in> F" "b \<in> F"
  and consistent: "\<And>a b. \<lbrakk> a \<in> F; (a,b) \<in> r \<rbrakk> \<Longrightarrow> b \<in> F"
  shows "(a,b) \<in> rtrancl_on F r"
  using assms(1-3)
proof (induction rule: converse_rtrancl_induct)
  case (step y z) then have "z \<in> F" by (rule_tac consistent) simp
  with step have "(z,b) \<in> rtrancl_on F r" by simp
  with step.prems \<open>(y,z) \<in> r\<close> \<open>z \<in> F\<close> show ?case
    using converse_rtrancl_on_into_rtrancl_on
    by metis
qed simp

lemma rtrancl_on_rtranclI:
  "(a,b) \<in> rtrancl_on F r \<Longrightarrow> (a,b) \<in> r\<^sup>*"
  by (induct rule: rtrancl_on_induct) simp_all

lemma rtrancl_on_sub_rtrancl:
  "rtrancl_on F r \<subseteq> r^*"
  using rtrancl_on_rtranclI
  by auto



end
