import Mathlib.Algebra.Group.Subgroup.Basic

theorem Subgroup.normal_iInf_normal {ι G : Type*} [Group G] {a : ι → Subgroup G} (norm : ∀ i : ι , (a i).Normal) : (iInf a).Normal := ⟨
  fun g g_in_iInf h => by
    rw [Subgroup.mem_iInf] at *
    exact fun i => (norm i).conj_mem g (g_in_iInf i) h
⟩
