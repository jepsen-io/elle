theory Elle
  imports Main "~/elle/graphs/Digraph" "~/elle/graphs/Arc_Walk"
begin

(*
datatype opType = Write | Read

record op =
  OpType      :: "opType"
  PreVersion  :: "version"
  WriteArg    :: "writeArg option"
  PostVersion :: "version"
  WriteRet    :: "writeRet option"

definition newRead :: "version \<Rightarrow> op" where
"newRead v \<equiv> \<lparr>OpType = Read, PreVersion = v, WriteArg = None, PostVersion = v, WriteRet = None\<rparr>"

definition newWrite :: "version \<Rightarrow> writeArg \<Rightarrow> version \<Rightarrow> writeRet \<Rightarrow> op" where
"newWrite v a v' r \<equiv> \<lparr>OpType = Write, PreVersion = v, WriteArg = Some a, PostVersion = v', WriteRet = Some r\<rparr>"

definition isRead :: "op \<Rightarrow> bool" where
"isRead op \<equiv> (OpType op) = Write"
*)

(* We're just summoning these types out of the ether, rather than parameterizing everything
in the damn proof *)
typedecl version
typedecl writeArg
typedecl writeRet

(* It's handy to talk about the argument and return values of an op regardless of type *)
datatype arg = WriteArg writeArg | ReadArg
datatype ret = WriteRet writeRet | ReadRet version

(* A couple names for deciding what type of function an op is *)
datatype opFunc = Read | Write

(* Abstract operations can be either reads or writes *)
datatype aop =
  ARead "version" |                                (* version *)
  AWrite "version" "writeArg" "version" "writeRet" (* pre, arg, post, retval *)

(* We also have observed operations, which are like abstract ops, except we might not know their
versions or return vals *)
datatype oop =
  ORead  "version option" |
  OWrite "version option" "writeArg" "version option" "writeRet option"

(* A bunch of basic functions on operations. We're gonna have two variants for each one, aFoo and
oFoo, for abstract and observed operations. I think we need typeclasses to define a function over
n types? *)
definition aFunc :: "aop \<Rightarrow> opFunc" where
"aFunc op \<equiv> (case op of
  (AWrite v a v' r)  \<Rightarrow> Write |
  (ARead v)          \<Rightarrow> Read)"

definition oFunc :: "oop \<Rightarrow> opFunc" where
"oFunc op \<equiv> case op of
  OWrite v a v' r \<Rightarrow> Write |
  ORead v         \<Rightarrow> Read"

definition aPreVersion :: "aop \<Rightarrow> version" where
"aPreVersion op \<equiv> case op of
  AWrite v a v' r \<Rightarrow> v |
  ARead v         \<Rightarrow> v"

definition oPreVersion :: "oop \<Rightarrow> version option" where
"oPreVersion op \<equiv> case op of
  OWrite v a v' r \<Rightarrow> v |
  ORead v         \<Rightarrow> v"

definition aPostVersion :: "aop \<Rightarrow> version" where
"aPostVersion op \<equiv> case op of
  AWrite v a v' r \<Rightarrow> v' |
  ARead v         \<Rightarrow> v"

definition oPostVersion :: "oop \<Rightarrow> version option" where
"oPostVersion op \<equiv> case op of
  OWrite v a v' r \<Rightarrow> v' |
  ORead v         \<Rightarrow> v"

(* Polymorphic-ish functions for getting arguments and retvals *)
definition aArg :: "aop \<Rightarrow> arg" where
"aArg op \<equiv> case op of
  AWrite v a v' r \<Rightarrow> WriteArg a |
  ARead v         \<Rightarrow> ReadArg"

definition oArg :: "oop \<Rightarrow> arg" where
"oArg op \<equiv> case op of
  OWrite v a v' r \<Rightarrow> WriteArg a |
  ORead v         \<Rightarrow> ReadArg"

definition aRet :: "aop \<Rightarrow> ret" where
"aRet op \<equiv> case op of
  AWrite v a v' r \<Rightarrow> WriteRet r |
  ARead v         \<Rightarrow> ReadRet v"

definition oRet :: "oop \<Rightarrow> (ret option)" where
"oRet op \<equiv> case op of
  OWrite v a v' (Some r)  \<Rightarrow> Some (WriteRet r) |
  OWrite v a v' None      \<Rightarrow> None |
  ORead (Some v)          \<Rightarrow> Some (ReadRet v) |
  ORead None              \<Rightarrow> None"

(* The return value of a read of a version should be that version *)
theorem read_ret: "(aRet (ARead x)) = (ReadRet x)"
  apply (simp add: aRet_def)
  done

(* Read pre and post versions are equal *)
theorem read_pre_eq_post: "let r = (ARead x) in (aPreVersion r) = (aPostVersion r)"
  apply (simp add: aPreVersion_def aPostVersion_def)
  done

(* Compare an option to a value; returns true if the option is None, or the values are the same. *)
primrec optionCompatible :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" where
"optionCompatible None y     = True" |
"optionCompatible (Some x) y = (x = y)"

text \<open>An observed operation is equivalent to an abstract operation iff they have the same type,
same argument, and the abstract operation's values are consistent with the observer's, where
present\<close>
definition opCompatible :: "oop \<Rightarrow> aop \<Rightarrow> bool" where
"opCompatible oop aop \<equiv> (oFunc oop = aFunc aop) \<and>
  (optionCompatible (oPreVersion oop) (aPreVersion aop)) \<and>
  (oArg oop = aArg aop) \<and>
  (optionCompatible (oPostVersion oop) (aPostVersion aop)) \<and>
  (optionCompatible (oRet oop) (aRet aop))"

text \<open>If two operations are compatible, then they have the same argument.\<close>
theorem op_compat_implies_same_args: "(opCompatible a b) \<Longrightarrow> (oArg a = aArg b)"
  apply (simp add:opCompatible_def)
  done

text \<open>A transaction has an ID number, a committed flag, and a list of abstract operations.\<close>
datatype aTxn = ATxn "nat" "bool" "aop list"

text \<open>An observed transaction is the same, except the abstract committed state might not be known.\<close>
datatype oTxn = OTxn "nat" "bool option" "oop list"

text \<open>An observed transaction is compatible with an abstract transaction iff they have compatible
committed states, and each of their operations is compatible.\<close>
primrec opListCompatible :: "oop list \<Rightarrow> aop list \<Rightarrow> bool" where
"opListCompatible [] aops = (case aops of [] \<Rightarrow> True | a # as \<Rightarrow> False)" |
"opListCompatible (oop # oops) aops = (case aops of
  []          \<Rightarrow> False |
  aop # aops  \<Rightarrow> (opCompatible oop aop) \<and> (opListCompatible oops aops))"

fun txnCompatible :: "oTxn \<Rightarrow> aTxn \<Rightarrow> bool" where
"txnCompatible (OTxn _ oCommitted oOps) (ATxn _ aCommitted aOps) =
  ((optionCompatible oCommitted aCommitted) \<and> (opListCompatible oOps aOps))"


subsection \<open>Version Graphs\<close>

text \<open>A version graph is a directed graph between versions. Edges in the graph correspond to
abstract writes. The version graph defines the structure of an object; what transitions are
possible.\<close>
datatype versionGraph = VersionGraph "(version, aop) pre_digraph"

(* Extract version graph digraph *)
primrec versionGraphDigraph :: "versionGraph \<Rightarrow> ((version, aop) pre_digraph)" where
"versionGraphDigraph (VersionGraph dg) = dg"

text \<open>A trace of x in a version graph is the uniquely defined walk from x_init to x. We define a
list where each cons cell represents a version and its successive write op.\<close>

(* lmao right of course this doesn't terminate
datatype trace = TraceCons "version" "aop" "trace" |
                 TraceTip "version"
text \<open>Given a version in a version graph, we return its trace if one exists.\<close>
fun findTrace2 :: "version \<Rightarrow> versionGraph \<Rightarrow> trace \<Rightarrow> trace option" where
"findTrace2 v vg tr = (case vg of (VersionGraph dg) \<Rightarrow> (
  let writes = (in_arcs dg v) in (
    if (Set.is_empty writes) then (Some tr)
    else if (Set.is_singleton writes) then (
      let w = (Set.the_elem writes); v' = ((Digraph.head dg) w) in (
        findTrace2 v' vg (TraceCons v' w tr)
    )) else None)))" *)

(* Can I write that a trace *exists*? *)

(* A path is a non-empty list of writes whose versions match *)
primrec isPath :: "(aop list) \<Rightarrow> bool" where
"isPath []        = False" |
"isPath (w # ws)  = (((aPostVersion w) = (aPreVersion w)) \<and>
                    ((ws = []) \<or> (isPath ws)))"

(* A path is in a graph if all its elements are arcs in that graph *)
primrec isPathInGraph :: "('a list) \<Rightarrow> (('v,'a) pre_digraph) \<Rightarrow> bool" where
"isPathInGraph []       g = True" |
"isPathInGraph (a # as) g = ((a \<in> (Digraph.arcs g)) \<and> (isPathInGraph as g))"

(* A trace is a path from an initial to final version in a version graph *)
definition isTrace :: "versionGraph \<Rightarrow> version \<Rightarrow> (aop list) \<Rightarrow> version \<Rightarrow> bool" where
"isTrace vg init trace ver \<equiv> ((init = (aPreVersion (hd trace))) \<and>
                              (isPath trace) \<and>
                              (ver = (aPostVersion (last trace))) \<and>
                              (isPathInGraph trace (versionGraphDigraph vg)))"

text \<open>An object has a key, an initial version and a version graph.\<close>
datatype object = Object "nat" "version" "versionGraph"

primrec objectVersionGraph :: "object \<Rightarrow> versionGraph" where
"objectVersionGraph (Object _ _ vg) = vg"

primrec allVersionsInVersionGraph :: "versionGraph \<Rightarrow> (version set)" where
"allVersionsInVersionGraph (VersionGraph vg) = (Digraph.verts vg)"

(* An object's initial value should be in its version graph. *)
primrec wfObject :: "object \<Rightarrow> bool" where
"wfObject (Object _ init vg) = (init \<in> allVersionsInVersionGraph vg)"

definition allVersionsInObject :: "object \<Rightarrow> (version set)" where
"allVersionsInObject obj \<equiv> (allVersionsInVersionGraph (objectVersionGraph obj))"

text \<open>An object is traceable iff every object has a unique trace.\<close>
primrec isTraceable :: "object \<Rightarrow> bool" where
"isTraceable (Object idx init vg) = ((wfObject (Object idx init vg)) \<and>
   (\<forall>v. (v \<in> (allVersionsInVersionGraph vg) \<longrightarrow>
     (\<exists>!tr. (isTrace vg init tr v)))))"

primrec initInObject :: "object \<Rightarrow> version" where
"initInObject (Object _ init _) = init"

(* A well-formed object has a version in it. *)
lemma traceable_l1: "(wfObject obj) \<Longrightarrow> (\<exists>ver. (ver \<in> (allVersionsInObject obj)))"
  apply (metis allVersionsInObject_def object.exhaust objectVersionGraph.simps wfObject.simps)
  done

(* A traceable object has an element with a path beginning in the initial version. *)
theorem traceable_existence: "isTraceable(obj) \<longrightarrow>
  (\<exists>v. ((v \<in> (allVersionsInObject obj)) \<and>
       (\<exists>path. isTrace (objectVersionGraph obj) (initInObject obj) path v)))"
  by (metis allVersionsInObject_def initInObject.simps isTraceable.simps object.exhaust
            objectVersionGraph.simps traceable_l1)

(* And every object has exactly one trace, kinda trivial but still *)
theorem traceable_all: "isTraceable(obj) \<Longrightarrow>
  (\<forall>v. ((v \<in> (allVersionsInObject obj)) \<longrightarrow>
       (\<exists>!path. isTrace (objectVersionGraph obj) (initInObject obj) path v)))"
proof -
  (* It just spit this out, can you BELIEVE!?!? *)
  assume a1: "isTraceable obj"
  { fix vv :: version and aas :: "aop list \<Rightarrow> aop list"
    have "\<exists>as. vv \<notin> allVersionsInObject obj \<or> aas as = as \<and>
         isTrace (objectVersionGraph obj) (initInObject obj) as vv \<or>
         isTrace (objectVersionGraph obj) (initInObject obj) as vv \<and> \<not>
         isTrace (objectVersionGraph obj) (initInObject obj) (aas as) vv"
      using a1 by (metis (no_types) allVersionsInObject_def initInObject.simps
                  isTraceable.simps object.exhaust objectVersionGraph.simps) }
  then have "\<forall>v. \<exists>as. \<forall>asa. v \<notin> allVersionsInObject obj \<or> asa = as \<and> 
            isTrace (objectVersionGraph obj) (initInObject obj) as v \<or>
            isTrace (objectVersionGraph obj) (initInObject obj) as v \<and> \<not>
            isTrace (objectVersionGraph obj) (initInObject obj) asa v"
    by metis
  then show ?thesis
    by metis
qed
 

(* less sure about this stuff... *)

subsection \<open>Version orders\<close>

text \<open>A version order is a map of objects to a list of versions of that object. The version order
encodes the sequence of versions that object took on in some history\<close>
datatype versionOrder = VersionOrder "(object, version list) map"

(* I haven't really figured out the sugar for quantification yet, so here's a function that
tells you if every element in a set satisfies some predicate. Why does no one document their
functions in Isabelle? *)
fun isEvery :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"isEvery pred xs = (\<not> (Set.is_empty (Set.filter pred xs)))"
value "isEvery (\<lambda>(x :: nat). x = 1) {2,3,1}"

(* Set comprehension demo *)
value "{(x :: nat). x \<in> {1,2,3} \<and> (x = 2)}"

(* Returns true if every k/v pair in a map satisfies (p k v) *)
definition mapIsEvery :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) map \<Rightarrow> bool" where
"mapIsEvery pred m \<equiv> (\<not> (Set.is_empty (Set.filter
  (\<lambda>k. (let v = (m k) in (case v of Some v \<Rightarrow> (pred k v) | None \<Rightarrow> False)))
  (Map.dom m))))"

text \<open>A well-formed version order means every list starts with the initial version of its object,
and, that the order list is distinct, and that the ordered versions are of that object. We check
this first for a specific object and list, then for all such object->list pairs in the version
order map\<close>
definition wfVersionOrderPred :: "object \<Rightarrow> (version list) \<Rightarrow> bool" where
"wfVersionOrderPred obj order = (case obj of (Object _ init (VersionGraph vg)) \<Rightarrow>
  ((distinct order) \<and>
   (init = (hd order)) \<and>
   ((set order) \<subseteq> (Digraph.verts vg))))"

definition wfVersionOrder :: "versionOrder \<Rightarrow> bool" where
"wfVersionOrder (VersionOrder vos) \<equiv> mapIsEvery wfVersionOrderPred vos"

subsection \<open>Histories\<close>

text \<open>An Adya History is a set of objects, a version order, and a set of transactions over them.\<close>
datatype history = History "object set" "versionOrder" "aTxn set"

