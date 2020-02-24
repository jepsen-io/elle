theory History
  imports Main HOL.Map Transaction VersionOrder
begin

section \<open>History\<close>

text \<open>An abstract history, as defined by Adya, is a set of objects, transactions over them,
and a version order.\<close>

datatype history = History "object set" "atxn set" "versionOrder"

primrec all_atxns :: "history \<Rightarrow> atxn set" where
"all_atxns (History obs txns vo) = txns"

text \<open>It's going to be handy to get every version, operation, every write, and read out of a
history. We say a history's versions and writes are those in its transaction set, not every
version in its objects.\<close>

instantiation history :: all_versions
begin
primrec all_versions_history :: "history \<Rightarrow> version set" where
"all_versions_history (History objs txns vo) = \<Union>{all_versions t | t. t \<in> txns}"
instance ..
end

instantiation history :: all_aops
begin
primrec all_aops_history :: "history \<Rightarrow> aop set" where
"all_aops_history (History objs txns vo) = \<Union>{all_aops t | t. t \<in> txns}"
instance ..
end

text \<open>We constrain the version order for each object to be compatible with some trace in that
object's version graph.\<close>

primrec key_version_order_is_in_object :: "keyVersionOrder \<Rightarrow> object \<Rightarrow> bool" where
"key_version_order_is_in_object (KeyVersionOrder k vl) obj = (
  (k = key obj) \<and> (\<exists>tr. (is_trace_of obj tr (last vl))))"

text \<open>A well-formed history satisfies this property for every key in the version order; there's got
to be a corresponding object where that version order is a legal trace.\<close>

primrec version_order_is_in_corresponding_object :: "history \<Rightarrow> bool" where
"version_order_is_in_corresponding_object (History objs txns vo) =
  (\<forall> kvo. kvo \<in> vo \<longrightarrow> (\<exists>obj. (obj \<in> objs) \<and> (key_version_order_is_in_object kvo obj)))"

text \<open>Histories also need to ensure that their transactions are over their objects. For every op
in the history, we ensure that op's key identifies an object in the history, that that op's versions
are in that object, and if it's a write that the write is in the transaction graph of that object.\<close>

primrec transactions_are_over_objects :: "history \<Rightarrow> bool" where
"transactions_are_over_objects (History objs txns vo) =
  (\<forall> op. (op \<in> (all_aops (History objs txns vo))) \<longrightarrow>
    (let k = (key op) in
      (\<exists>obj. (k = (key obj)) \<and>
             (obj \<in> objs) \<and>
             ((all_versions op) \<subseteq> (all_versions obj)) \<and>
             (if Read = (op_type op) then True else op \<in> (all_aops obj)))))"



text \<open>We need to be able to discuss whether a specific transaction wrote a given key and version, in
a history.\<close>

(*
primrec wrote :: "history \<Rightarrow> atxn \<Rightarrow> key \<Rightarrow> version \<Rightarrow> bool" where
"wrote h t k v = "
*)

text \<open>A well-formed history is made up of well formed objects, transactions, and a version order,
and ensures transactions are over objects, and the version orders are in their corresponding
objects.\<close>

primrec wf_history :: "history \<Rightarrow> bool" where
"wf_history (History objs txns vo) = (let h = (History objs txns vo) in
                 (\<forall>obj. (obj \<in> objs) \<longrightarrow> (wf_object obj)) \<and>
                 (\<forall>t. (t \<in> txns) \<longrightarrow> (wf_atxn t)) \<and>
                 (wf_version_order vo) \<and>
                 ((transactions_are_over_objects h) \<and>
                 (version_order_is_in_corresponding_object h)))"

text \<open>We'd like to know if two versions occurred consecutively in the version order for some key.\<close>
primrec is_next_in_history :: "history \<Rightarrow> key \<Rightarrow> version \<Rightarrow> version \<Rightarrow> bool" where
"is_next_in_history (History objs txns vo) k v1 v2 =
  (\<exists>kvo. (key kvo = k) \<and> (kvo \<in> vo) \<and>
         (is_next_in_key_version_order kvo v1 v2))"

end