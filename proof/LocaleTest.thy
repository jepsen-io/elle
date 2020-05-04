theory LocaleTest
  imports Main
begin

(* A box for things of some unspecified type 'a *)
datatype 'a box = Box "'a"

(* A typeclass that can make boxes?

class boxable =
  fixes makebox :: "'o \<Rightarrow> ('a box)"
*)

(* This complains "multiple variables in type specification, and I can't seem to parameterize
the typeclass with type variables itself. Shit. *)

locale menagerie =
  fixes animal_type :: "'at"
  and favorite :: "'a"
begin

(* We can't use animal_type at the type level here, so... while you CAN apparently pass types
to locales when constructing intepretations, those types can't be used in definitions. Which...
I guess makes sense, cuz the definitions here should typecheck on their *own*. Right? *)
definition feed :: "'at \<Rightarrow> bool" where
"feed a \<equiv> (case a of favorite \<Rightarrow> True | x \<Rightarrow> False)"
end

interpretation pets: menagerie nat 0 .

