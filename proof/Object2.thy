theory Object2
  imports Main
begin

section \<open>Datatypes\<close>

text \<open>We begin by defining a datatype as an initial value plus a transition function, which takes a
verson and argument to a (value', ret-val) tuple. We define a datatype to encapsulate this tuple:\<close>

datatype ('v, 'r) write_out = WriteOut 'v 'r

primrec write_out_value :: "('v, 'r) write_out \<Rightarrow> 'v" where
"write_out_value (WriteOut v r) = v"

primrec write_out_ret :: "('v, 'r) write_out \<Rightarrow> 'r" where
"write_out_ret (WriteOut v r) = r"

text \<open>And a locale which fixes the initial value and transition function w.\<close>

locale data_type =
  fixes init :: "'v"
  and w :: "'v \<Rightarrow> 'a \<Rightarrow> ('v, 'r) write_out"
begin

text \<open>Given a sequence of write arguments, we can construct a function which applies those arguments
in sequence.\<close>

primrec apply_args :: "'v \<Rightarrow> 'a list \<Rightarrow> 'v" where
"apply_args v [] = v" |
"apply_args v (a # as) = apply_args (write_out_value (w v a)) as"

text \<open>Some lemmata around apply_args\<close>

lemma apply_args_Cons: "apply_args v (a#as) = apply_args (write_out_value (w v a)) as"
  by auto

text \<open>A database is traceable if, for any version, there exists exactly one sequence of args that
leads to that version.\<close>

definition is_traceable :: "bool" where
"is_traceable \<equiv> \<forall> args1 args2 . apply_args init args1 = apply_args init args2 \<longrightarrow> args1 = args2"

end

locale traceable_data_type = data_type init w for init w +
  assumes traceable:"is_traceable"
begin

text \<open>Here, we prove facts about traceable data types.\<close>

end

section \<open>Append-only lists\<close>

text \<open>We begin by showing that list append over lists of naturals can form a data type.\<close>

definition list_append_w :: "'x list \<Rightarrow> 'x \<Rightarrow> ('x list, bool) write_out" where
"list_append_w xs x \<equiv> WriteOut (xs @ [x]) True"

value "list_append_w [a, b] c"

interpretation list_append: data_type "[]" list_append_w .

text \<open>We want to show this datatype is traceable. First, we prove that applying a sequence of args
produces that list of args itself.\<close>

value "list_append.apply_args x [a,b]"

lemma list_append_args_are_value:"list_append.apply_args [] xs = xs"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    apply (simp add: data_type.apply_args_Cons)

qed

interpretation list_append_traceable:traceable_data_type "[]" "list_append_w"
  using list_append.is_traceable_def traceable_data_type_def

end
