theory InferredAnomaly
  imports Main Observation
begin

section \<open>Inferred Non-Cyclic Anomalies\<close>

text \<open>Using observations, we set out to infer anomalies which should (we hope) be present in
any compatible observation. We prefix these versions of the anomalies with 'i' for 'inferred'.\<close>

definition has_ig1a :: "observation \<Rightarrow> bool" where
"has_ig1a obs \<equiv> (\<exists>t1 t2 k v. t1\<in> all_otxns obs \<and>
                              t2 \<in> all_otxns obs \<and>
                              o_is_committed t1 = Some False \<and>
                              o_is_committed t2 = Some True \<and>
                              is_recoverable obs k v t1 \<and>
                              (ORead k (Some v)) \<in> (all_oops obs))"

theorem ig1a_sound "has_ig1a obs \<longrightarrow> (\<forall>i. i \<in> interpretations obs \<longrightarrow> has_g1a (history i))"


end
