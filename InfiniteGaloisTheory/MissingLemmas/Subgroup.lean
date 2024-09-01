import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

theorem Subgroup.normal_iInf_normal {ι G : Type*} [Group G] {a : ι → Subgroup G} (norm : ∀ i : ι , (a i).Normal) : (iInf a).Normal := ⟨
  fun g g_in_iInf h => by
    rw [Subgroup.mem_iInf] at *
    exact fun i => (norm i).conj_mem g (g_in_iInf i) h
⟩

open Pointwise
theorem QuotientGroup.preimage_mk_eq_coset {G : Type*} [Group G] {H : Subgroup G} (i : G ⧸ H) : QuotientGroup.mk ⁻¹' {i} = (Quotient.out' i) • ↑H := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hxi
    rw [← hxi]
    let ⟨t, ht⟩ := QuotientGroup.mk_out'_eq_mul H x
    rw [ht]
    use t⁻¹
    simp only [SetLike.mem_coe, inv_mem_iff, SetLike.coe_mem, smul_eq_mul, mul_inv_cancel_right, and_self]
  intro ⟨t, hht, ht⟩
  simp only [smul_eq_mul] at ht
  have : i = QuotientGroup.mk (Quotient.out' i) := by exact Eq.symm (QuotientGroup.out_eq' i)
  rw [this]
  refine QuotientGroup.eq.mpr ?h.mpr.a
  rw [← ht]; simp only [mul_inv_rev, inv_mul_cancel_right, inv_mem_iff]; exact hht
