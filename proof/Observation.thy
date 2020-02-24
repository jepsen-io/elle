theory Observation
  imports Main History
begin

section \<open>Observations\<close>

text \<open>Fundamentally, an observation is a set of objects and observed transactions over them.\<close>

datatype observation = Observation "object set" "otxn set"

text \<open>We define some basic accessors...\<close>

primrec all_otxns :: "observation \<Rightarrow> otxn set" where
"all_otxns (Observation objs txns) = txns"

instantiation observation :: all_objects
begin
primrec all_objects_observation :: "observation \<Rightarrow> object set" where
"all_objects_observation (Observation objs txns) = objs"
instance ..
end

instantiation observation :: all_versions
begin
primrec all_versions_observation :: "observation \<Rightarrow> version set" where
"all_versions_observation (Observation objs txns) = \<Union>{all_versions t | t. t \<in> txns}"
instance ..
end

instantiation observation :: all_oops
begin
primrec all_oops_observation :: "observation \<Rightarrow> oop set" where
"all_oops_observation (Observation objs txns) = \<Union>{all_oops t | t. t \<in> txns}"
instance ..
end

text \<open>A well-formed observation is made up of well-formed objects and transactions, and its
transactions are over those objects.\<close>

primrec wf_observation :: "observation \<Rightarrow> bool" where
"wf_observation (Observation objs txns) =
  ((\<forall>obj. obj \<in> objs \<longrightarrow> wf_object obj) \<and>
   (\<forall>t. t \<in> txns \<longrightarrow> (wf_otxn t \<and> (\<forall>oop. (oop \<in> (all_oops t)) \<longrightarrow>
                                          (\<exists>!obj. (obj \<in> objs) \<and> ((key oop) = (key obj)))))))"


text \<open>We say an observation is compatible with a history via relation m if they have the same
object set, the same number of transactions, and m is a bijective mapping from observed transactions
in the observation to compatible abstract transactions in the history.\<close>

definition is_compatible_observation :: "observation \<Rightarrow> (otxn \<Rightarrow> atxn) \<Rightarrow> history \<Rightarrow> bool" where
"is_compatible_observation obs m h =
  ((all_objects obs = all_objects h) \<and>
   (\<forall>otxn. otxn \<in> (all_otxns obs) \<longrightarrow> (is_compatible_txn otxn (m otxn))))"


section \<open>Interpretations\<close>

text \<open>An interpretation of an observation O is a history H and a bijection M which translates
operations in O to compatible observations in H. Interpretation is a reserved word, so...\<close>

datatype interp = Interp "observation" "(otxn \<Rightarrow> atxn)" "history"

primrec history :: "interp \<Rightarrow> history" where
"history (Interp obs m h) = h"

text \<open>We say f is a total bijection between a and b iff f is bijective and every a maps to a b.
I feel like there should be something for this in Isabelle already but I'm not sure.\<close>

definition total_bij :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
"total_bij f as bs \<equiv> ((bij f) \<and> (\<forall>a. (a \<in> as) \<longrightarrow> ((f a) \<in> bs)))"

(* I can't even show this? Really? *)
lemma "(total_bij f as bs \<and> (b = (f a))) \<longrightarrow> (b \<in> bs)"
  apply (simp add:total_bij_def)
  apply auto
  oops

(* Huh, would have thought this would be easy *)
lemma total_bij_image1: "(total_bij f a b) \<Longrightarrow> ((f`a) = b)"
  apply (simp add: total_bij_def)

  oops

text \<open>Well-formed interpretations are made up of a well-formed observation, a bijection between
observed and abstract transactions, and a well-formed history, such that the observation and 
the history are compatible via that bijection.\<close>

primrec wf_interpretation :: "interp \<Rightarrow> bool" where
"wf_interpretation (Interp obs m h) = ((wf_observation obs) \<and>
                                       (wf_history h) \<and>
                                       (total_bij m (all_otxns obs) (all_atxns h)) \<and>
                                       (is_compatible_observation obs m h))"

text \<open>This lets us talk about corresponding transactions via that bijection m.\<close>

primrec corresponding_atxn :: "interp \<Rightarrow> otxn \<Rightarrow> atxn" where
"corresponding_atxn (Interp obs m h) otxn = (m otxn)"

primrec corresponding_otxn :: "interp \<Rightarrow> atxn \<Rightarrow> otxn" where
"corresponding_otxn (Interp obs m h) atxn = (THE otxn. atxn = m otxn)"

text \<open>These are invertible, thanks to m being bijective.\<close>

lemma "(corresponding_otxn (Interp obs h m) atxn) \<in> (all_otxns obs)"


lemma corresponding_invertible: "(corresponding_otxn i (corresponding_atxn i t)) = t"
  oops

section \<open>Recoverability\<close>

text \<open>Recoverability allows us to (in some cases) map a version of some key to a specific
observed transaction which must have produced it. To start, we figure out when a transaction
could have written a particular version of an object: some write resulting in this version of the
object is compatible with a write in the transaction.\<close>

definition could_have_been_written_by :: "object \<Rightarrow> version \<Rightarrow> otxn \<Rightarrow> bool" where
"could_have_been_written_by obj v t \<equiv> (\<exists>aw ow. aw \<in> awrites_of obj v \<and>
                                               ow \<in> all_owrites t \<and>
                                               is_compatible_op ow aw)"

(* might have this wrong *)
lemma "((could_have_been_written_by obj v ot) \<and> (is_compatible_txn ot atxn)) \<longrightarrow>
        (\<exists>v0 a r. (AWrite k v0 a v r) \<in> all_awrites atxn)"
  oops


text \<open>Given an observation, we say a version v of key k is recoverable to a transaction t if t is
the only transaction which could have written that v of k.\<close>

definition is_recoverable :: "observation \<Rightarrow> key \<Rightarrow> version \<Rightarrow> otxn \<Rightarrow> bool" where
"is_recoverable obs k v ot \<equiv> (let obj = (THE ob. ob \<in> all_objects obs \<and> key ob = k) in
                                (could_have_been_written_by obj v ot) \<and>
                                (\<exists>!t. t \<in> all_otxns obs \<and> could_have_been_written_by obj v t))"




end