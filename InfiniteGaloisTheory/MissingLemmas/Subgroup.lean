/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

open scoped Pointwise

namespace Subgroup

/-- Intersection of normal subgroups is a normal subgroup. -/
theorem normal_iInf_normal {ι G : Type*} [Group G] {a : ι → Subgroup G} (norm : ∀ i : ι , (a i).Normal) : (iInf a).Normal := ⟨
  fun g g_in_iInf h => by
    rw [Subgroup.mem_iInf] at *
    exact fun i => (norm i).conj_mem g (g_in_iInf i) h
⟩

/-- An isomorphism maps a normal Subgroup to a normal Subgroup. -/
theorem map_equiv_normal {G G': Type*} [Group G] [Group G'] (f : G ≃* G')
    (H : Subgroup G) [hn: H.Normal] : (H.map f.toMonoidHom).Normal := by
  have h : map f.toMonoidHom ⊤ = ⊤ := map_top_of_surjective f (MulEquiv.surjective f)
  apply normalizer_eq_top.mp
  rw [← h, ← normalizer_eq_top.mpr hn, map_equiv_normalizer_eq H f]

section

variable (G : Type*) [Group G] (H : Subgroup G)

lemma mem_normalCore (g : G) : g ∈ H.normalCore ↔ ∀ (b : G), b * g * b⁻¹ ∈ H := by rfl

lemma normalCore_eq_iInf_conjAct : H.normalCore = ⨅ (g : ConjAct G), g • H := by
  ext g
  simp_rw [mem_normalCore, mem_iInf, mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h x
    specialize h (x⁻¹)
    simpa
  · intro h x
    specialize h (x⁻¹)
    simpa using h

end

end Subgroup

namespace QuotientGroup

theorem preimage_mk_eq_coset {G : Type*} [Group G] {H : Subgroup G} (i : G ⧸ H) : QuotientGroup.mk ⁻¹' {i} = (Quotient.out' i) • ↑H := by
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

end QuotientGroup
