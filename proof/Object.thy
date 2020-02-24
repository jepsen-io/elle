theory Object
  imports
    Main Op "graphs/Digraph"
begin

section \<open>Version Graphs\<close>

text \<open>A version graph is a directed graph between versions, whose arcs (edges) are writes.\<close>

type_synonym "versionGraph" = "(version, aop) pre_digraph"

section \<open>Paths\<close>

text \<open>A path is a non-empty list of abstract writes such that each write's postversion connects to
the next write's preversion.\<close>

type_synonym "path" = "aop list"

primrec is_path :: "aop list \<Rightarrow> bool" where
"is_path [] = False" |
"is_path (w1 # ws) = (case ws of [] \<Rightarrow> True | (w2 # _) \<Rightarrow>
                      ((post_version w1) = (pre_version w2)) \<and> (is_path ws))"

lemma "is_path [AWrite k [0] 1 [1] [], AWrite k [1] 2 [2] []]"
  apply auto
  done

text \<open>We can also retrieve every version along a path, including the preversion of the first
write, and the postversion of the last write.\<close>

primrec path_versions :: "aop list \<Rightarrow> version list" where
"path_versions [] = []" |
"path_versions (w # ws) = ((apre_version w) # (map apost_version (w # ws)))"

text \<open>We say a path is in a version graph if every write in the path is in the version graph too.\<close>
primrec is_path_in_graph :: "aop list \<Rightarrow> versionGraph \<Rightarrow> bool" where
"is_path_in_graph [] g = True" |
"is_path_in_graph (w # ws) g = ((w \<in> (Digraph.arcs g)) \<and> (is_path_in_graph ws g))"



section \<open>Objects\<close>

text \<open>We define an Object as a key, an initial version, and a digraph over versions, where arcs
are writes."\<close>

datatype object = Object "key" "version" "versionGraph"

text \<open>Some basic accessors for objects\<close>

instantiation object :: keyed
begin
primrec key_object :: "object \<Rightarrow> key" where
"key_object (Object k i g) = k"
instance ..
end

primrec initial_version :: "object \<Rightarrow> version" where
"initial_version (Object k i g) = i"

primrec version_graph :: "object \<Rightarrow> versionGraph" where
"version_graph (Object k i g) = g"

instantiation object :: all_versions
begin
primrec all_versions_object :: "object \<Rightarrow> version set" where
"all_versions (Object k i g) = (Digraph.verts g)"
instance ..
end

instantiation object :: all_aops
begin
primrec all_aops_object :: "object \<Rightarrow> aop set" where
"all_aops_object (Object k i g) = (Digraph.arcs g)"
instance ..
end

section \<open>Traces\<close>

text \<open>A trace is a path in some object's version graph which connects the initial version to some
chosen version.\<close>

definition is_trace_of :: "object \<Rightarrow> path \<Rightarrow> version \<Rightarrow> bool" where
"is_trace_of obj p v \<equiv> ((is_path p) \<and>
                       (is_path_in_graph p (version_graph obj)) \<and>
                       ((initial_version obj) = (apre_version (hd p))) \<and>
                       (v = (apost_version (last p))))"

text \<open>We say an object is fully reachable if every element other than init has a trace.\<close>

definition is_fully_reachable :: "object \<Rightarrow> bool" where
"is_fully_reachable obj \<equiv> (\<forall>v. (v \<in> (all_versions obj)) \<longrightarrow> (\<exists>p. (is_trace_of obj p v)))"



text \<open>We can now define a well-formed object: they are fully reachable, and their initial version
is in the version graph. That second part might be redundant.\<close>

definition wf_object_init_in_graph :: "object \<Rightarrow> bool" where
"wf_object_init_in_graph obj \<equiv> ((initial_version obj) \<in> (all_versions obj))"

definition wf_object :: "object \<Rightarrow> bool" where
"wf_object obj \<equiv> (wf_object_init_in_graph obj) \<and>
                 (is_fully_reachable obj)"


text \<open>Now, we aim to include a new property: traceability\<close>

text \<open>Does this object have exactly one write resulting in a version?\<close>

definition version_has_only_one_write :: "object \<Rightarrow> version \<Rightarrow> bool" where
"version_has_only_one_write obj v \<equiv> (\<exists>!w. ((apost_version w) = v) \<and> (w \<in> (all_awrites obj)))"

definition every_version_has_only_one_write :: "object \<Rightarrow> bool" where
"every_version_has_only_one_write obj \<equiv> (\<forall>v. (v \<in> (all_versions obj)) \<longrightarrow>
                                              (version_has_only_one_write obj v))"

definition every_version_has_at_most_one_write :: "object \<Rightarrow> bool" where
"every_version_has_at_most_one_write obj \<equiv> (\<forall>v. (v \<in> (all_versions obj)) \<longrightarrow>
                                                ((\<not>(\<exists>w. (apost_version w) = v)) \<or>
                                                (\<exists>!w. (apost_version w) = v)))"

text \<open>We say an object is traceable if it has exactly one trace for every version other than
the initial version.\<close>

definition is_traceable :: "object \<Rightarrow> bool" where
"is_traceable obj \<equiv> (\<forall>v. (v \<in> (all_versions obj) \<longrightarrow> (\<exists>!p. (is_trace_of obj p v))))"

text \<open>Traceability implies that every version has at most one write.\<close>

(* TODO *)


subsection \<open>Implementations of objects\<close>


text \<open>Our digraphs need sets of vertices and arcs. We can write infinite sets, but for debugging and
examples, it's nice to think about finite domains. Let's construct the set of singleton lists up to
size s...\<close>
(* This throws a well-sortedness error value "{(v :: version). True}" *)

primrec nats_up_to :: "nat \<Rightarrow> nat list" where
"nats_up_to 0       = []" |
"nats_up_to (Suc n) = (n # (nats_up_to n))"
value "nats_up_to 2"

(* Takes a list and returns every variant of that list but starting with nats up to n. *)
definition tack_on_nats_up_to :: "nat \<Rightarrow> nat list \<Rightarrow> nat list list" where
"tack_on_nats_up_to n xs \<equiv> (map (\<lambda>x. (x # xs)) (nats_up_to n))"
value "tack_on_nats_up_to 3 (1 # [])"

(* Map and concatenate *)
definition mapcat :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"mapcat f xs \<equiv> (concat (map f xs))"
value "mapcat nats_up_to (1 # 2 # 3 # [])"

(* Fixed lists *)
primrec lists_of_n_nats_up_to_m :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
"lists_of_n_nats_up_to_m 0        m = ([] # [])" |
"lists_of_n_nats_up_to_m (Suc n)  m = (mapcat (tack_on_nats_up_to m) (lists_of_n_nats_up_to_m n m))"
value "lists_of_n_nats_up_to_m 2 2"

(* Variable lists *)
definition lists_of_nats_up_to :: "nat \<Rightarrow> nat list list" where
"lists_of_nats_up_to m \<equiv> (mapcat (\<lambda>n. (lists_of_n_nats_up_to_m (Suc n) m))
                                 (nats_up_to m))"

text \<open>Given a set of versions, an initial version, and a write function which takes a current
version and an argument to a resulting version and return value, we can build an object.\<close>

(*
 (AWrite k v1 a v2 r) | v1 a v2 r. (v1 \<in> domain) \<and>
                                   (v2 \<in> domain) \<and> 
                                   (f v1 a) = (v2,r)},
*)

text \<open>We define a finite object constructor for debugging purposes--this version is executable.\<close>
definition smol_object :: "version list \<Rightarrow> writeArg list \<Rightarrow> version \<Rightarrow>
                           (version \<Rightarrow> writeArg \<Rightarrow> (version \<times> writeRet)) \<Rightarrow> key \<Rightarrow> object" where
"smol_object vs args init f k \<equiv> (Object k init
  \<lparr>verts = (set vs),
   arcs  = (set (mapcat (\<lambda>v1. (mapcat (\<lambda>v2. (mapcat (\<lambda>a.
                  (let (v2,r) = (f v1 a) in
                    (if (v2 \<in> (set vs)) then ((AWrite k v1 a v2 r) # []) else [])))
                  args)) vs)) vs)),
   tail  = apost_version,
   head  = apre_version\<rparr>)"

text \<open>And an object whose values are single-element sets up to the number n, such that writes
always overwrite the current value, and return values are always the empty list.\<close>

definition smol_register :: "nat \<Rightarrow> key \<Rightarrow> object" where
"smol_register n k \<equiv> (smol_object (lists_of_n_nats_up_to_m 1 n)
                                  (nats_up_to n)
                                  (0 # [])
                                  (\<lambda>ver arg. ((arg # []), []))
                                  k)"
value "smol_register 2 2"

text \<open>It's easier to prove properties of infinitely defined registers.\<close>

definition register :: "key \<Rightarrow> object" where
"register k \<equiv> (Object k [0] \<lparr>verts = {[v] | v. v \<in> Nats},
                             arcs  = {(AWrite k [v1] a [a] []) | v1 a. v1 \<in> Nats \<and> a \<in> Nats},
                             tail = apost_version,
                             head = apre_version\<rparr>)"

text \<open>We show that all finite registers can only reach values up to [n].\<close>

lemma "(all_versions (smol_register n (0::nat))) = (set (map (\<lambda>x.[x]) (nats_up_to n)))"
  apply (simp add:smol_register_def mapcat_def tack_on_nats_up_to_def
        nats_up_to_def smol_object_def)
  done

text \<open>And that finite nonempty registers are well-formed.\<close>

(* Not working yet
lemma "(0 < n) \<longrightarrow> wf_object (smol_register n k)"
  apply (simp add:wf_object_def wf_object_init_in_graph_def smol_register_def initial_version_def
         smol_object_def mapcat_def tack_on_nats_up_to_def nats_up_to_def)
  apply (induct_tac n)
   apply simp
  apply auto
  done

text \<open>The single-element register is traceable\<close>

lemma smol_singleton_register_traceable: "is_traceable (smol_register n k)"
  apply (simp add:is_traceable_def all_versions_def smol_register_def smol_object_def mapcat_def
tack_on_nats_up_to_def is_trace_of_def nats_up_to_def is_path_def is_path_in_graph_def
apre_version_def apost_version_def)
  (* huh not sure *)
  oops
*)

text \<open>The set of versions of an infinite register is all single-element lists.\<close>

lemma register_versions [simp]: "(all_versions (register k)) = {[x] | x. x \<in> Nats}"
  apply (simp add:register_def)
  done


lemma helper1: "(initial_version (register k)) = [0]"
  by (simp add: register_def)

lemma helper2: "AWrite k [0] (Suc 0) [Suc 0] [] \<in> arcs (version_graph (register k))"
  apply (simp add:register_def)
  by (metis Nats_1 One_nat_def)

lemma zero_in_N: "0 \<in> Nats"
  by auto

lemma n_in_N_implies_suc_in_N: "(n \<in> Nats) \<longrightarrow> (Suc n \<in> Nats)"
  by (metis (full_types) Nats_1 Nats_add One_nat_def add.right_neutral add_Suc_right)

(* REALLY? *)
lemma n_in_N [simp]: "(n::nat) \<in> Nats"
proof -
  obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
    f1: "\<forall>p n. (\<not> p 0 \<or> p (nn p) \<and> \<not> p (Suc (nn p))) \<or> p n"
    using nat_induct by moura
  have "(0::nat) \<in> \<nat> \<and> (nn (\<lambda>n. n \<in> \<nat>) \<notin> \<nat> \<or> Suc (nn (\<lambda>n. n \<in> \<nat>)) \<in> \<nat>)"
    using n_in_N_implies_suc_in_N by force
  then show ?thesis
    using f1 by (metis (no_types))
qed

(* I am... shocked this is this complicated *)
lemma succ_n_in_N [simp]: "(Suc n) \<in> Nats"
  by (simp add:n_in_N)

lemma helper3: "AWrite k [Suc 0] n [n] [] \<in> arcs (version_graph (register k))"
  by (simp add:register_def)

text \<open>There is a single-write trace to any version.\<close>

lemma register_one_trace: "is_trace_of (register k) [AWrite k [0] n [n] []] [n]"
  apply (simp add:is_trace_of_def register_def)
  done

text \<open>There is a second trace to any version going 0\<rightarrow>1\<rightarrow>v\<close>

lemma register_two_trace: "is_trace_of (register k) [(AWrite k [0] 1 [1] []),
                                                     (AWrite k [1] n [n] [])] [n]"
  unfolding is_trace_of_def
  apply auto
    apply (simp add:helper2)
   apply (simp add:helper3)
  by (simp add: helper1)

lemma register_has_a_trace: "\<exists>p. is_trace_of (register k) p [n]"
  using register_two_trace by blast

(* not working yet
lemma register_has_two_traces: "let r = (register k) in \<exists>p1 p2. (is_trace_of r p1 [n]) \<and>
                                                                (is_trace_of r p2 [n]) \<and>
                                                                (p \<noteq> q)"
proof-
  { fix x assume "x = 2" }
  using register_one_trace
  using register_two_trace

lemma register_not_traceable: "~(is_traceable (register k))"
  oops
*)

end