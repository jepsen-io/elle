theory Scratch
  imports Main Observation
begin

text \<open>So, you can't have a typeclass return a type parameter. Let's see if we can define a type with
no properties, then later, assert some properties *of* that type and use them in a proof. So... some
`foo` exists. We don't know what it is.\<close>

typedecl foo

text \<open>We can make a container for foo\<close>

datatype box = Box "foo"

text \<open>We can use foo for equality...\<close>

lemma "(x :: foo) \<noteq> (y :: foo) \<longrightarrow> (Box x) \<noteq> (Box y)"
  apply auto
  done

lemma "(x :: foo) = (y :: foo) \<longrightarrow> (Box x) = (Box y)"
  apply auto
  done

text \<open>We can define a typeclass which returns foos...\<close>

class openable =
  fixes open1 :: "'a \<Rightarrow> foo"

instantiation box :: openable
begin
primrec open1 :: "box \<Rightarrow> foo" where
"open1 (Box f) = f"
instance ..
end

text \<open>Now it'd be nice if we could show something trivial, like... if foo is, say, a nat, then open1
returns a nat. If we were using type parameters, I'd make a "box nat", but since we're NOT using
type parameters... I want to write, like, (foo = nat) \<Rightarrow> is_nat (openable x)" but I have no idea how\<close>

text \<open>I think what I want here is maybe... a locale? Let's try that...\<close>

locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl [intro, simp]: "le x x"
    and anti_sym [intro]: "\<lbrakk>le x y; le y x\<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk>le x y; le y z\<rbrakk> \<Longrightarrow> le x z"

text \<open>So... what we've done here is assert a le function exists, and it obeys these laws, but we
haven't actually said what le is. le could operate over cats or cargo ships. It could be < or >. Can
I define a locale that returns a type parameter?\<close>

locale openable2 =
  fixes open2 :: "'a \<Rightarrow> 'b"

text \<open>Huh. So... all I've said here is that a binary function exists. What about... making a box for
a type parameter? That's something we can't do with typeclasses...\<close>

datatype 'a abstract_box = AbstractBox "'a"
locale boxable =
  fixes box :: "'a \<Rightarrow> ('b abstract_box)"

text \<open>Okay, so I can define a boxable function which returns something with type parameters. Note
that our box is over a different type, so we could, I dunno, take strings and constantly return
AbstractBox 2 or something.\<close>

