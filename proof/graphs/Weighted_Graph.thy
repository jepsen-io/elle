(* Title:  Weighted_Graph.thy
   Author: Lars Noschinski, TU München
*)

theory Weighted_Graph
imports
  Digraph
  Arc_Walk
  Complex_Main
begin

section \<open>Weighted Graphs\<close>

type_synonym 'b weight_fun = "'b \<Rightarrow> real"

context wf_digraph begin

definition awalk_cost :: "'b weight_fun \<Rightarrow> 'b awalk \<Rightarrow> real" where
  "awalk_cost f es = sum_list (map f es)"

lemma awalk_cost_Nil[simp]: "awalk_cost f [] = 0"
  unfolding awalk_cost_def by simp

lemma awalk_cost_Cons[simp]: "awalk_cost f (x # xs) = f x + awalk_cost  f xs"
  unfolding awalk_cost_def by simp

lemma awalk_cost_append[simp]:
  "awalk_cost f (xs @ ys) = awalk_cost f xs + awalk_cost f ys"
  unfolding awalk_cost_def by simp

end

end
