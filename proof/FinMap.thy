theory FinMap
  imports Main HOL.Map
begin

section \<open>Finite Maps\<close>

text \<open>A finite map can be thought of as a set of (k,v) pairs, with unique keys. Think an erlang
proplist. We use this as a wrapper around Isabelle's Maps because those maps use optional, and it
makes quantification over kv pairs kind of messy.\<close>

definition keys :: "('a,'b) map \<Rightarrow> 'a set" where
"keys m = dom m"

definition vals :: "('a,'b) map \<Rightarrow> 'b set" where
"vals m = ran m"

definition kv_pairs :: "('a,'b) map \<Rightarrow> ('a \<times> 'b) set" where
"kv_pairs m = {(k,v) | k v. (k \<in> (keys m)) \<and> ((Some v) = (m k))}"

text \<open>A function for building map literals out of keys and values.\<close>
definition map1 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) map" where
"map1 k v \<equiv> (Map.empty(k:=Some v))"

definition map2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) map" where
"map2 k1 v1 k2 v2 \<equiv> (Map.empty(k1:=Some v1, k2:=Some v2))"

end