theory IDSG
  imports Main Observation
begin

section \<open>Inferred Version Order\<close>

text \<open>We begin by inferring a version order based on traceability and recoverability. TODO: we're
not handling intermediate dependencies yet.\<close>

text \<open>Pick a version from the committed read set with the longest trace.\<close>

value "((\<lambda>x::nat. (Suc x)) ` ({1,2}))"

definition o_committed_txns :: "observation \<Rightarrow> otxn set" where
"o_committed_txns obs \<equiv> {t \<in> (all_otxns obs). o_definitely_committed t}"

definition o_committed_reads :: "observation \<Rightarrow> oop set" where
"o_committed_reads obs \<equiv> \<Union>(all_oreads ` (o_committed_txns obs))"

definition o_committed_versions_k :: "observation \<Rightarrow> key \<Rightarrow> version set" where
"o_committed_versions_k obs k \<equiv>
  \<Union>(all_versions ` {r. r \<in> (o_committed_reads obs) \<and> ((key r) = k)})"

definition x_longest :: "observation \<Rightarrow> k \<Rightarrow> version"
"x_longest obs \<equiv> (let vs (o_committed_versions obs k) in
                    (THE v. (v \<in> vs) \<and> \<not>(\<exists>v2. (trace_length v1) < (trace_length v2))

TODO what a mess; pick up here later

section \<open>Inferred Transaction Dependencies\<close>



text \<open>We use recoverability to map observed versions in a history back into writes, and infer
dependencies between them.\<close>

definition 

end