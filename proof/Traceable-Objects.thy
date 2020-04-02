theory "Traceable-Objects"
imports Main
begin

section \<open>A few properties of foldl\<close>

lemma l1:"foldl (o) a (rev (x#xs)) = (foldl (o) a (rev xs)) o x"
  by simp

lemma l2:"foldl (o) a (x#xs) = a o (foldl (o) x xs)"
proof (induct "rev xs" arbitrary:a x xs)
  case Nil
  then show ?case
    by auto 
next
  case (Cons a xa)
  then show ?case
    by (metis (no_types, lifting) append_Cons comp_assoc l1 rev.simps(2) rev_swap) 
qed

lemma l3:"foldl (o) x xs = x o (foldl (o) id xs)"
  by (metis comp_id foldl_Cons l2)

text \<open>TODO: this could be generalized to multiplicative commutative monoids 
(functions with the composition operation are a multiplicative commutative monoid).\<close>

section \<open>Data types and traceability\<close>

locale data_type = 
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" \<comment> \<open>the transition function of the data type\<close>
  and init :: "'a"
begin

definition exec \<comment> \<open>a state transformer corresponding to applying all operations in order\<close>
  where "exec ops \<equiv> foldl (o) id (map f ops)" \<comment> \<open>@{term "(o)"} is function composition \<close>

lemma exec_Cons:"exec (x#xs) = (f x) o (exec xs)"
  using exec_def l3 by force

lemma exec_Nil:"exec [] = id"
  by (simp add: exec_def)

definition is_traceable \<comment> \<open>A state has a unique history from the initial state\<close>
  where "is_traceable \<equiv> \<forall> ops\<^sub>1 ops\<^sub>2 . exec ops\<^sub>1 init = exec ops\<^sub>2 init \<longrightarrow> ops\<^sub>1 = ops\<^sub>2"
  
end

locale traceable_data_type = data_type f init for f init +
  assumes traceable:"is_traceable"
begin

text \<open>Prove some facts about traceable datatypes...\<close>

end

section \<open>Append-only lists are traceable\<close>

interpretation list_data_type: data_type "(#)" "[]" .

lemma l4:"list_data_type.exec xs [] =  xs"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: list_data_type.exec_Nil) 
next
  case (Cons a xs) 
  then show ?case 
    by (simp add: data_type.exec_Cons)
qed

interpretation list_traceable:traceable_data_type "(#)" "[]"
  using l4 list_data_type.is_traceable_def traceable_data_type_def by fastforce

text \<open>Now the facts proved about traceable datatypes are available for append-only lists.\<close>

end