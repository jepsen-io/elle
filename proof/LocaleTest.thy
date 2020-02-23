theory LocaleTest
  imports Main
begin

(* A box for things of some unspecified type 'a *)
datatype 'a box = Box "'a"

(* A typeclass that can make boxes? *)
class boxable =
  fixes makebox :: "'o \<Rightarrow> ('a box)"

(* This complains "multiple variables in type specification, and I can't seem to parameterize
the typeclass with type variables itself. Shit. *)