theory Anomaly
  imports Main DSG Observation
begin

section \<open>Non-Cyclic Anomalies\<close>

text \<open>We are now ready to encode notions of Adya's anomalies. An aborted read, or g1a, implies some
pair of transactions exist such that one wrote v1 and aborted, and another read v1 and committed.\<close>

definition has_g1a :: "history \<Rightarrow> bool" where
"has_g1a h \<equiv> (\<exists>t1 t2 k v1 a v2 r. (t1 \<in> (all_atxns h)) \<and>
                                  (t2 \<in> (all_atxns h)) \<and>
                                  (\<not>(a_is_committed t1)) \<and>
                                  (a_is_committed t2) \<and>
                                  (AWrite k v1 a v2 r) \<in> (all_aops t1) \<and>
                                  (ARead k v2) \<in> (all_aops t2))"

text \<open>An empty history does not have an aborted read.\<close>

lemma "\<not>(has_g1a (History {(register 1)} {} {(KeyVersionOrder 1 [[0]])}))"
  by (simp add:has_g1a_def)

text "But this history does: we write 1 and fail to commit, then read it! We don't actually
have to constrain the version order for this to happen, either."

lemma "has_g1a (History {(register 1)}
                        {(ATxn [(AWrite 1 [0] 1 [1] [])] False),
                         (ATxn [(ARead 1 [1])] True)}
                        kvo)"
  using has_g1a_def by fastforce

(* TODO: intermediate read, dirty update *)

section \<open>Cyclic Anomalies\<close>

text \<open>In an G0 anomaly, a cycle exists in the DSG composed purely of write dependencies.\<close>

definition has_g0 :: "history \<Rightarrow> bool" where
"has_g0 h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> ((path_dep_types path) = {WW}))"

text \<open>For example...\<close>

lemma ww_depends_ex:
  assumes "(distinct [x,y]) \<and> (distinct [v0,v1,v2])"
  shows "ww_depends (History objs
                         {(ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True),
                          (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)}
                         {(KeyVersionOrder x [v0,v1,v2]),
                          (KeyVersionOrder y [v0,v1,v2])})
                      (ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True)
                      (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)"
  apply (simp add:ww_depends_def)
proof-
  obtain t1 t2 where "t1 = (ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True) \<and>
                      t2 = (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)"
    by blast
  oops


lemma
  assumes "(distinct [x,y]) \<and> (distinct [v0,v1,v2])"
  shows "has_g0 (History objs
                         {(ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True),
                          (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)}
                         {(KeyVersionOrder x [v0,v1,v2]),
                          (KeyVersionOrder y [v0,v1,v2])})"
  apply (simp add:has_g0_def dsg_def path_def cycle_def)
  oops

text \<open>A G1c anomaly is a cycle comprised of write-write and write-read dependencies. We diverge from
Adya here in classifying G0 and G1c as distinct classes; feels more useful to distinguish them.\<close>

definition has_g1c :: "history \<Rightarrow> bool" where
"has_g1c h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> ((path_dep_types path) = {WW,WR}))"

text \<open>And a G2 anomaly is a cycle involving read-write dependencies.\<close>

definition has_g2 :: "history \<Rightarrow> bool" where
"has_g2 h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> (RW \<in> (path_dep_types path)))"



end