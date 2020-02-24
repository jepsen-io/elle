theory Op
  imports Main
begin

section \<open>Keys, Versions, and Operations\<close>

text \<open>Our database is conceptually modeled as a map of keys to values. We choose natural numbers
for our keys as a convenient identifier--we just need to tell them apart.\<close>
type_synonym "key" = "nat"

text \<open>It'd be nice to define our versions, arguments, and return values as polymorphic type
parameters. However, owing to what I think is a limitation in Isabelle's typeclass system, we can't.
What we CAN do is fix our versions, arguments, and retvals as lists of naturals, naturals, and lists
of naturals, respectively. We can use this representation for lists, sets, counters, and registers
easily, by defining different types of graphs. Also, we won't have to carry these type parameters on
everything.\<close>

type_synonym "version" = "nat list"
type_synonym "writeArg" = "nat"
type_synonym "writeRet" = "nat list"

text \<open>Reads and writes are different types of operations. We're going to want to distinguish
them.\<close>

datatype opType = Read | Write

text \<open>Reads and writes have different types of arguments and return values. However, it's going to
be convenient to talk about and compare their arguments and return values without caring what type
of operation we performed. We define wrapper types for arguments and return values here.\<close>

datatype arg = WriteArg "writeArg" | ReadArg
datatype ret = WriteRet "writeRet" | ReadRet "version"

text \<open>An operation acts on the state of some key, taking a preversion of an object and, using an
argument, producing a postversion and a return value. In general, we don't know exactly what the
versions and return value are; we represent these as options.\<close>

class keyed =
  fixes key :: "'a \<Rightarrow> key"

class op =
  fixes op_type      :: "'a \<Rightarrow> opType"
  fixes pre_version  :: "'a \<Rightarrow> version option"
  fixes arg          :: "'a \<Rightarrow> arg"
  fixes post_version :: "'a \<Rightarrow> version option"
  fixes ret          :: "'a \<Rightarrow> ret option"

text \<open>We now define two types of operations. Abstract operations (beginning with a) have definite
versions and values. Observed operations may not know their versions and return values. Reads take
no argument and return their current version; writes may change their versions somehow.\<close>

datatype aop =
  ARead  "key" "version" |
  AWrite "key" "version" "writeArg" "version" "writeRet"

datatype oop =
  ORead  "key" "version option" |
  OWrite "key" "version option" "writeArg" "version option" "writeRet option"

text \<open>A few accessors for when we don't want to deal with optionals...\<close>

primrec apre_version :: "aop \<Rightarrow> version" where
"apre_version (ARead k v)           = v" |
"apre_version (AWrite k v1 a v2 r)  = v1"

primrec aret :: "aop \<Rightarrow> ret" where
"aret (ARead k v)           = (ReadRet v)" |
"aret (AWrite k v1 a v2 r)  = (WriteRet r)"

primrec apost_version :: "aop \<Rightarrow> version" where
"apost_version (ARead k v)           = v" |
"apost_version (AWrite k v1 a v2 r)  = v2"

definition aversions_in_op :: "aop \<Rightarrow> version set" where
"aversions_in_op op \<equiv> {apre_version op, apost_version op}"

text \<open>These accessors allow us to extract keys, versions, etc from all types of operations in
a uniform way.\<close>

instantiation aop :: keyed
begin
primrec key_aop :: "aop \<Rightarrow> key" where
"key_aop (ARead k v)           = k" |
"key_aop (AWrite k v1 a v2 r)  = k"
instance ..
end

instantiation aop :: op
begin
primrec op_type_aop :: "aop \<Rightarrow> opType" where
"op_type_aop (ARead k v)           = Read" |
"op_type_aop (AWrite k v1 a v2 r)  = Write"

primrec pre_version_aop :: "aop \<Rightarrow> version option" where
"pre_version_aop (ARead k v)          = Some v" |
"pre_version_aop (AWrite k v1 a v2 r) = Some v1"

primrec arg_aop :: "aop \<Rightarrow> arg" where
"arg_aop (ARead k v)           = ReadArg" |
"arg_aop (AWrite k v1 a v2 r)  = WriteArg a"

primrec post_version_aop :: "aop \<Rightarrow> version option" where
"post_version_aop (ARead k v)           = Some v" |
"post_version_aop (AWrite k v1 a v2 r)  = Some v2"

primrec ret_aop :: "aop \<Rightarrow> ret option" where
"ret_aop (ARead k v)           = Some (ReadRet v)" |
"ret_aop (AWrite k v1 a v2 r)  = Some (WriteRet r)"

instance ..
end

text \<open>As a quick test of these accessors...\<close>
lemma "arg (ARead k v) = ReadArg"
  by auto

lemma "pre_version (AWrite k v1 a v2 r) = Some v1"
  by auto

lemma "post_version (AWrite k v1 a v2 r) = Some v2"
  by auto

lemma "(key (ARead k v1)) = (key (AWrite k v2 a v3 r))"
  by auto

text \<open>Moving on to accessors for observed operations...\<close>

instantiation oop :: keyed
begin
primrec key_oop :: "oop \<Rightarrow> key" where
"key_oop (ORead k v)           = k" |
"key_oop (OWrite k v1 a v2 r)  = k"
instance ..
end

instantiation oop :: op
begin

primrec op_type_oop :: "oop \<Rightarrow> opType" where
"op_type_oop (ORead k v)           = Read" |
"op_type_oop (OWrite k v1 a v2 r)  = Write"

primrec pre_version_oop :: "oop \<Rightarrow> version option" where
"pre_version_oop (ORead k v)          = v" |
"pre_version_oop (OWrite k v1 a v2 r) = v1"

primrec arg_oop :: "oop \<Rightarrow> arg" where
"arg_oop (ORead k v)           = ReadArg" |
"arg_oop (OWrite k v1 a v2 r)  = WriteArg a"

primrec post_version_oop :: "oop \<Rightarrow> version option" where
"post_version_oop (ORead k v)           = v" |
"post_version_oop (OWrite k v1 a v2 r)  = v2"

primrec ret_oop :: "oop \<Rightarrow> ret option" where
"ret_oop (ORead k v)           = (case v of Some v \<Rightarrow> Some (ReadRet v) | None \<Rightarrow> None)" |
"ret_oop (OWrite k v1 a v2 r)  = (case r of Some r \<Rightarrow> Some (WriteRet r) | None \<Rightarrow> None)"

instance ..
end

text \<open>And as a quick check...\<close>
lemma "(post_version (ORead k1 (Some v))) =
       (pre_version (OWrite k2 (Some v) a None None))"
  by auto

text \<open>We're going to be asking a lot about "the set of all versions in <something>".\<close>
class all_versions =
  fixes all_versions :: "'a \<Rightarrow> version set"


instantiation aop :: all_versions
begin
primrec all_versions_aop :: "aop \<Rightarrow> version set" where
"all_versions_aop (ARead k v) = {v}" |
"all_versions_aop (AWrite k v1 a v2 r) = {v1, v2}"
instance ..
end

instantiation oop :: all_versions
begin
primrec all_versions_oop :: "oop \<Rightarrow> version set" where
"all_versions_oop (ORead k v) = (case v of None \<Rightarrow> {} | (Some v) \<Rightarrow> {v})" |
"all_versions_oop (OWrite k v1 a v2 r) = (case v1 of
                                    None \<Rightarrow> (case v2 of None \<Rightarrow> {} | (Some v2) \<Rightarrow> {v2}) |
                               (Some v1) \<Rightarrow> (case v2 of None \<Rightarrow> {v1} | (Some v2) \<Rightarrow> {v1, v2}))"
instance ..
end

text \<open>... And all keys in something \<close>
class all_keys =
  fixes all_keys :: "'a \<Rightarrow> key set"

text \<open>And similarly, we're going to want to talk about all operations in a transaction, version
graph, object, history, observation, etc...\<close>

class all_aops =
  fixes all_aops :: "'a \<Rightarrow> aop set"

class all_oops =
  fixes all_oops :: "'a \<Rightarrow> oop set"

text \<open>And if you have the set of all ops, you can filter that to the set of writes or reads.\<close>

definition all_owrites :: "'a::all_oops \<Rightarrow> oop set" where
"all_owrites a = {op. (op \<in> (all_oops a)) \<and> ((op_type op = Write))}"

definition all_oreads :: "'a::all_oops \<Rightarrow> oop set" where
"all_oreads a = {op. (op \<in> (all_oops a)) \<and> ((op_type op = Read))}"

definition all_awrites :: "'a::all_aops \<Rightarrow> aop set" where
"all_awrites a = {op. (op \<in> (all_aops a)) \<and> ((op_type op = Write))}"

definition all_areads :: "'a::all_aops \<Rightarrow> aop set" where
"all_areads a = {op. (op \<in> (all_aops a)) \<and> ((op_type op = Read))}"

text \<open>We now define a notion of compatibility, which says whether an observed operation could
correspond to some abstract operation. The idea here is that the database executed the abstract
operation, but that we don't know, due to the client protocol, or perhaps due to missing responses,
exactly what happened. We compare Options to actual values, ensuring that either the optional is
None (e.g. we don't know), or if it's Some, that the values are equal.

I'd like to do this as a typeclass, but without multi-type-parameter typeclasses, we can't
write a generic function over a \<Rightarrow> b \<Rightarrow> bool. This seems like something I'm likely to mess up,
so instead, we write a family of compatibility functions with type names.\<close>

primrec is_compatible_option :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" where
"is_compatible_option None     y = True" |
"is_compatible_option (Some x) y = (x = y)"

text \<open>An observed operation is compatible with an abstract operation if their types, keys,
versions, arguments, and return values are all compatible.\<close>
definition is_compatible_op :: "oop \<Rightarrow> aop \<Rightarrow> bool" where
"is_compatible_op oop aop \<equiv>
  (((op_type oop) = (op_type aop)) \<and>
   ((key oop) = (key aop)) \<and>
   (is_compatible_option (pre_version oop)  (apre_version aop)) \<and>
   ((arg oop) = (arg aop)) \<and>
   (is_compatible_option (ret oop)          (aret aop)) \<and>
   (is_compatible_option (post_version oop) (apost_version aop)))"

end