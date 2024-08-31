import Mathlib.Algebra.Group.Subgroup.Basic

lemma Subgroup.normal_iInf_normal {ι G : Type*} [Group G] {a : ι → Subgroup G} (norm : ∀ i : ι , (a i).Normal) : (iInf a).Normal :=by
  constructor
  intro g g_in_iInf h
  simp only [Subgroup.mem_iInf] at *
  intro i
  specialize norm i
  specialize g_in_iInf i
  apply norm.conj_mem g g_in_iInf
