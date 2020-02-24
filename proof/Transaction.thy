theory Transaction
  imports
    Main
    "./Object"
begin

section \<open>Transactions\<close>

text \<open>A transaction is a list of object operations followed by (possibly) a commit or abort
operation. In the Adya formalism, a transaction ends in a commit or abort operation; we also
need to allow for observed operations where the operation outcome is unknown. To simplify our
types, we model the committed state as a separate field.\<close>

(* I literally can't figure out how to write a class that returns classes, so we're gonna
do this with explicit abstract and observed functions for everything. *)

(* TODO: add an ID for transactions so you can execute the same ops more than once *)

datatype atxn = ATxn "aop list" "bool"
datatype otxn = OTxn "oop list" "bool option"

text \<open>Some basic accessors.\<close>

primrec a_ops :: "atxn \<Rightarrow> aop list" where
"a_ops (ATxn ops _) = ops"

primrec o_ops :: "otxn \<Rightarrow> oop list" where
"o_ops (OTxn ops _) = ops"

primrec a_is_committed :: "atxn \<Rightarrow> bool" where
"a_is_committed (ATxn _ committed) = committed"

primrec o_is_committed :: "otxn \<Rightarrow> bool option" where
"o_is_committed (OTxn _ committed) = committed"

primrec o_definitely_committed :: "otxn \<Rightarrow> bool" where
"o_definitely_committed (OTxn _ c) = ((Some True) = c)"

primrec o_definitely_aborted :: "otxn \<Rightarrow> bool" where
"o_definitely_aborted (OTxn _ c) = ((Some False = c))"

instantiation atxn :: all_versions
begin
primrec all_versions_atxn :: "atxn \<Rightarrow> version set" where
"all_versions_atxn (ATxn ops _) = \<Union>{(all_versions op) | op. op \<in> (set ops)}"
instance ..
end

instantiation otxn :: all_versions
begin
primrec all_versions_otxn :: "otxn \<Rightarrow> version set" where
"all_versions_otxn (OTxn ops _) = \<Union>{all_versions op | op. op \<in> (set ops)}"
instance ..
end

instantiation atxn :: all_aops
begin
primrec all_aops_atxn :: "atxn \<Rightarrow> aop set" where
"all_aops_atxn (ATxn ops _) = set ops"
instance ..
end

instantiation otxn :: all_oops
begin
primrec all_oops_otxn :: "otxn \<Rightarrow> oop set" where
"all_oops_otxn (OTxn ops _) = set ops"
instance ..
end

text \<open>We define the external abstract writes of a transaction as the writes w such that no other
write to the same key as w followed w in that transaction. We start with functions to extract
the first and last objects by key from a list...\<close>

primrec first_per_keys :: "'a::keyed list \<Rightarrow> (key,'a) map" where
"first_per_keys [] = Map.empty" |
"first_per_keys (x # xs) = ((first_per_keys xs)((key x):=(Some x)))"

primrec ext_awrites :: "atxn \<Rightarrow> aop set" where
"ext_awrites (ATxn ops _) = (ran (first_per_keys (rev ops)))"

primrec ext_areads :: "atxn \<Rightarrow> aop set" where
"ext_areads (ATxn ops _) = (ran (first_per_keys ops))"

text \<open>A brief test...\<close>

lemma "(let wx1 = (AWrite 1 [0] 1 [1] []);
            wx2 = (AWrite 1 [1] 2 [2] []);
            wy3 = (AWrite 2 [0] 0 [3] []) in
        {wx1,wy3} = (ext_awrites (ATxn [wx1,wy3,wx1] c)))"
  apply (simp add: ext_awrites_def ran_def)
  by (smt Collect_cong Suc_inject insert_compr numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_One
          singleton_iff zero_neq_one)



text \<open>A well-formed transaction...\<close>

primrec wf_atxn :: "atxn \<Rightarrow> bool" where
"wf_atxn (ATxn ops committed) = True"

text \<open>For observed transactions, we require that when committed, they definitely have a return
value.\<close>

primrec wf_otxn :: "otxn \<Rightarrow> bool" where
"wf_otxn (OTxn ops committed) = (if ((Some True) = committed) then
                                  (\<forall>op. (op \<in> set ops) \<longrightarrow> ((ret op) \<noteq> None))
                                  else True)"

text \<open>We define compatibility in terms of operation and committed state compatibility\<close>

fun is_compatible_op_list :: "oop list \<Rightarrow> aop list \<Rightarrow> bool" where
"is_compatible_op_list [] [] = True" |
"is_compatible_op_list (a # as) [] = False" |
"is_compatible_op_list [] (oo # os) = False" |
"is_compatible_op_list (aop # aops') (oop # oops') =
  ((is_compatible_op aop oop) \<and> (is_compatible_op_list aops' oops'))"

lemma is_compatible_op_list_size: "(is_compatible_op_list l1 l2) \<Longrightarrow> ((length l1) = (length l2))"
  oops

(* My kingdom for indicating shadowing in binding exprs: every short name in Isabelle is taken *)
definition is_compatible_txn :: "otxn \<Rightarrow> atxn \<Rightarrow> bool" where
"is_compatible_txn otx atx \<equiv> ((is_compatible_op_list (o_ops otx) (a_ops atx)) \<and>
                              (is_compatible_option (o_is_committed otx) (a_is_committed atx)))"


text \<open>Some lemmata around compatibility\<close>

lemma is_compatible_txn_op_count: "is_compatible_txn otxn atxn \<Longrightarrow>
  ((size (o_ops otxn)) = (size (a_ops atxn)))"
  oops


end