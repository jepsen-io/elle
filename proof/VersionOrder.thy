theory VersionOrder
  imports Main Op FinMap
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

end