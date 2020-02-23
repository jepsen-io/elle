theory PolymorphismTest
  imports Main
begin

(* This is a little scratchpad/demo for polymorphic functions; I dunno whether I can just write
them directly with pattern matching or if I need typeclasses *)

(* Unrelated types of animals with a leg count and, for warydog, a wariness state *)
datatype cat = Cat "bool list"
datatype dog = Dog "nat" |
               WaryDog "nat" "bool"

class pet =
  fixes legs :: "'a => nat"
  fixes friendly :: "'a => bool"

(* Make cats treatable as pets! Note that these monomorphic function names are *magic*: Isabelle
expects them in this format when it generates... whatever its eldritch equivalent of type dispatch
tables are for polymorphic functions*)

instantiation cat :: pet
begin
primrec legs_cat :: "cat \<Rightarrow> nat" where
"legs_cat (Cat leg_count) = (length leg_count)"

definition friendly_cat :: "cat \<Rightarrow> bool" where
"friendly_cat cat = True"

(* "Trivial instantiation proof" -- I don't understand this but I don't think I need to yet *)
instance ..
end

(* OK now do dogs *)
instantiation dog :: pet
begin
primrec legs_dog :: "dog \<Rightarrow> nat" where
"legs_dog (Dog leg_count) = leg_count" |
"legs_dog (WaryDog leg_count wary) = leg_count"

fun friendly_dog :: "dog \<Rightarrow> bool" where
"friendly_dog (WaryDog _ wary) = (\<not> wary)" |
"friendly_dog d = True"

instance ..
end

value "legs (Cat (True # False # []))"
value "legs (WaryDog 4 False)"
value "friendly (WaryDog 2 False)"
(* extremely joe damato voice: COOOOOL *)

(* A typeclass can't be used as a type. I assume there's some sort of constraint syntax which
lets us say "'a is in class pet" but I can't find it so far
definition friendly_four :: "pet \<Rightarrow> bool" where
"friendly_four p \<equiv> ((friendly p) \<and> (4 = legs p))"
*)

(* Can we define it with a type parameter and rely on unification to figure it out for us? No,
this complains "'a is not of sort pet"
definition friendly_four2 :: "'a \<Rightarrow> bool" where
"friendly_four2 p \<equiv> ((friendly p) \<and> (4 = legs p))"
*)

(* lmao oh right of course. Sorts/Kinds/higher-rank-types are types of types. We put a type on
the type! *)
definition friendly_four3 :: "('a::pet) \<Rightarrow> bool" where
"friendly_four3 p \<equiv> ((friendly p) \<and> (4 = legs p))"

(* OK, now... how do we define a class that returns a class? We can't use a type parameter because
typeclasses can only have a single polymorphism site...
class shelter =
  fixes adopt :: "'a \<Rightarrow> 'b::pet"
*)

(* Can we define a type synonym, so the type variable doesn't appear lexically in the class?
No, this throws Undefined type name: "a_pet
type_synonym "a_pet" = "'a::pet" *)

class shelter =
  fixes adopt :: "'a \<Rightarrow> a_pet"