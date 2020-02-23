theory Anomaly
  imports Main Transaction History
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

section \<open>Cyclic Anomalies\<close>

text \<open>We say a transation ww-depends on another if t1 installed some version v1 of k, and t2 wrote
v2, such that v1 came immediately before v2 in the version order of k.\<close>

definition ww_depends :: "history \<Rightarrow> atxn \<Rightarrow> atxn \<Rightarrow> bool" where
"ww_depends h t1 t2 \<equiv> \<exists>w1 w2.
  (a_is_committed t1) \<and>
  (a_is_committed t2) \<and>
  (w1 \<in> ext_awrites t1) \<and>
  (w2 \<in> ext_awrites t2) \<and>
  ((key w1) = (key w1)) \<and>
  (is_next_in_history h (key w1) (apost_version w1) (apost_version w2))"

text \<open>In an immediate G0 anomaly, a pair of transactions ww-depend on each other.\<close>

definition has_immediate_g0 :: "history \<Rightarrow> bool" where
"has_immediate_g0 h \<equiv> (\<exists>t1 t2.
  (t1 \<in> (all_atxns h)) \<and>
  (t2 \<in> (all_atxns h)) \<and>
  (ww_depends h t1 t2) \<and>
  (ww_depends h t2 t1))"

text \<open>But I can't prove this example yet. :(\<close>

lemma "has_immediate_g0
  (let x = 1; y = 2 in
    (History {(register x), (register y)}
     {(ATxn [(AWrite x [0] 1 [1] []), (AWrite y [1] 2 [2] [])] True),
      (ATxn [(AWrite y [0] 1 [1] []), (AWrite x [1] 2 [2] [])] True)}
     {(KeyVersionOrder x [[0], [1]]),
      (KeyVersionOrder y [[0], [1]])}))"
  oops

end