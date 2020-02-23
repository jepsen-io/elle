theory History
  imports Main HOL.Map Transaction FinMap
begin

section \<open>Orders\<close>

text \<open>For our purposes, we're interested in total orders. Our orders aren't exactly total orders,
because they might contain a single element, like the initial sets. They're mathematically "chains",
but we encode them here as lists of distinct elements.\<close>

text \<open>In order to be an order, we need a list to be distinct.\<close>

definition wf_order :: "('a list) \<Rightarrow> bool" where
"wf_order ord \<equiv> (distinct ord)"

text \<open>We're going to be asking frequently for a pair of successive versions in some order.\<close>
primrec is_next :: "('a list) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_next []       a b = False" |
"is_next (x # xs) a b = (case xs of
                          []        \<Rightarrow> False |
                          (y # ys)  \<Rightarrow> ((a = x \<and> b = y) \<or> (is_next xs a b)))"

text \<open>We say that order a is compatible with b iff a's elements occur in b, in the same order.\<close>
fun is_compatible_order :: "('a list) \<Rightarrow> ('a list) \<Rightarrow> bool" where
"is_compatible_order []       []       = True" |
"is_compatible_order (x # xs) []       = False" |
"is_compatible_order []       (y # ys) = True" |
"is_compatible_order (x # xs) (y # ys) =
  (if x = y then (is_compatible_order xs ys)
            else (is_compatible_order (x # xs) ys))"




section \<open>Version Orders\<close>

text \<open>A key version order is a key associated with an order of distinct versions.
It captures the notion that some key's value went through a particular series of versions
over time.\<close>

datatype keyVersionOrder = KeyVersionOrder "key" "version list"

instantiation keyVersionOrder :: keyed
begin
primrec key_keyVersionOrder :: "keyVersionOrder \<Rightarrow> key" where
"key_keyVersionOrder (KeyVersionOrder k vl) = k"
instance ..
end

text \<open>Is v1 right before v2 in this version order?\<close>

primrec is_next_in_key_version_order :: "keyVersionOrder \<Rightarrow> version \<Rightarrow> version \<Rightarrow> bool" where
"is_next_in_key_version_order (KeyVersionOrder k vl) v1 v2 = (is_next vl v1 v2)"

text \<open>A version order is a set of key version orders with unique keys.\<close>

type_synonym "versionOrder" = "keyVersionOrder set"

text \<open>We define basic accessors for these too.\<close>

definition version_order_keys :: "versionOrder \<Rightarrow> key set" where
"version_order_keys vo \<equiv> {k. (\<exists>vl. (KeyVersionOrder k vl) \<in> vo)}"

definition version_order_version_lists :: "versionOrder \<Rightarrow> version list set" where
"version_order_version_lists vo \<equiv> {vl. (\<exists>k. (KeyVersionOrder k vl) \<in> vo)}"

text \<open>We'll often want to assert that given a set of objects, they're uniquely identified by
some function f.\<close>

definition unique_by :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
"unique_by f s \<equiv> (\<forall>el. (el \<in> s) \<longrightarrow> (\<exists>!x. x = (f el)))"

text \<open>We enforce uniqueness and well-formed orders.\<close>

definition wf_version_order :: "versionOrder \<Rightarrow> bool" where
"wf_version_order vo = ((unique_by key vo) \<and>
                        (\<forall>vl. (vl \<in> (version_order_version_lists vo)) \<longrightarrow> wf_order vl))"



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