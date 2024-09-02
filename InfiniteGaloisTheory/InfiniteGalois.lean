/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import InfiniteGaloisTheory.Basic

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

open Pointwise

lemma fixingSubgroup_IsClosed (L : IntermediateField k K) [IsGalois k K] :
  IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) where
    isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ h => by
      apply mem_nhds_iff.mpr
      have := (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mp h
      push_neg at this
      rcases this with ⟨y,yL,ne⟩
      use σ • ((FiniteGaloisIntermediateField.adjoin k {y}).1.fixingSubgroup : Set (K ≃ₐ[k] K))
      constructor
      · intro f hf
        rcases (Set.mem_smul_set.mp hf) with ⟨g,hg,eq⟩
        simp only [Set.mem_compl_iff, SetLike.mem_coe, ←eq]
        apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mpr
        push_neg
        use y
        simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
        have := (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp hg y <|
          FiniteGaloisIntermediateField.adjoin_simple_le_iff.mp fun ⦃x⦄ a ↦ a
        simp only [AlgEquiv.smul_def] at this
        rw [this]
        exact ne
      · constructor
        · have : IsOpen ((FiniteGaloisIntermediateField.adjoin k {y}).1.fixingSubgroup
            : Set (K ≃ₐ[k] K)) := by
            apply IntermediateField.fixingSubgroup_isOpen
          exact IsOpen.smul this σ
        · apply Set.mem_smul_set.mpr
          use 1
          simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true]
          exact congrFun rfl

lemma fixedField_bot [IsGalois k K] :
  IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    unfold IntermediateField.fixedField FixedPoints.intermediateField MulAction.fixedPoints at hx
    simp only [Subtype.forall, Subgroup.mem_top, Subgroup.mk_smul, AlgEquiv.smul_def, true_implies,
      IntermediateField.mem_mk] at hx
    have id : ∀ (σ : K ≃ₐ[k] K), σ x = x := hx
    let Lx := ((FiniteGaloisIntermediateField.adjoin k {x}))
    have mem : x ∈ Lx.1 := FiniteGaloisIntermediateField.adjoin_simple_le_iff.mp fun ⦃x_1⦄ a ↦ a
    have : IntermediateField.fixedField (⊤ : Subgroup (Lx ≃ₐ[k] Lx)) = ⊥ := by
      rw [←IntermediateField.fixingSubgroup_bot k Lx]
      exact IsGalois.fixedField_fixingSubgroup ⊥
    have : ⟨x,mem⟩ ∈ (⊥ : IntermediateField k Lx) := by
      rw [←this]
      unfold IntermediateField.fixedField FixedPoints.intermediateField MulAction.fixedPoints
      simp only [Subtype.forall, Subgroup.mem_top, Subgroup.mk_smul, AlgEquiv.smul_def,
        true_implies, IntermediateField.mem_mk]
      show ∀ (f : Lx ≃ₐ[k] Lx), f ⟨x,mem⟩ = ⟨x,mem⟩
      intro f
      rcases AlgEquiv.restrictNormalHom_surjective (K₁ := Lx) K f with ⟨σ,hσ⟩
      apply Subtype.val_injective
      rw [←hσ, ←InfiniteGalois.restrict_eq σ x Lx mem, id σ]
    rcases IntermediateField.mem_bot.mp this with ⟨y,hy⟩
    apply_fun Subtype.val at hy
    exact IntermediateField.mem_bot.mpr ⟨y,hy⟩
  · exact OrderBot.bot_le (IntermediateField.fixedField ⊤)

lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
  IntermediateField.fixedField L.fixingSubgroup = L := by
  letI : IsGalois L K := inferInstance
  have := InfiniteGalois.fixedField_bot (k := L) (K := K)
  apply le_antisymm
  · intro x hx
    unfold IntermediateField.fixedField FixedPoints.intermediateField MulAction.fixedPoints at hx
    simp only [Subtype.forall, Subgroup.mem_top, Subgroup.mk_smul, AlgEquiv.smul_def, true_implies,
      IntermediateField.mem_mk] at hx
    have id : ∀ σ ∈ L.fixingSubgroup, σ x = x := hx
    let Lx := ((FiniteGaloisIntermediateField.adjoin L {x}))
    have mem : x ∈ Lx.1 := FiniteGaloisIntermediateField.adjoin_simple_le_iff.mp fun ⦃x_1⦄ a ↦ a
    have : IntermediateField.fixedField (⊤ : Subgroup (Lx ≃ₐ[L] Lx)) = ⊥ := by
      rw [←IntermediateField.fixingSubgroup_bot L Lx]
      exact IsGalois.fixedField_fixingSubgroup ⊥
    have : ⟨x,mem⟩ ∈ (⊥ : IntermediateField L Lx) := by
      rw [←this]
      unfold IntermediateField.fixedField FixedPoints.intermediateField MulAction.fixedPoints
      simp only [Subtype.forall, Subgroup.mem_top, Subgroup.mk_smul, AlgEquiv.smul_def,
        true_implies, IntermediateField.mem_mk]
      show ∀ (f : Lx ≃ₐ[L] Lx), f ⟨x,mem⟩ = ⟨x,mem⟩
      intro f
      rcases AlgEquiv.restrictNormalHom_surjective (K₁ := Lx) K f with ⟨σ,hσ⟩
      apply Subtype.val_injective
      rw [←hσ, ←InfiniteGalois.restrict_eq σ x Lx mem]
      dsimp
      have := id <| (IntermediateField.fixingSubgroupEquiv L).symm σ
      simp only [SetLike.coe_mem, true_implies] at this
      convert this
    rcases IntermediateField.mem_bot.mp this with ⟨y,hy⟩
    have : ((algebraMap { x // x ∈ L } { x // x ∈ Lx.1 }) y).1 = x := by rw [hy]
    rw [←this]
    have : ((algebraMap { x // x ∈ L } { x // x ∈ Lx.1 }) y).1 = y := rfl
    rw [this]
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr fun ⦃x⦄ a ↦ a

lemma fixingSubgroup_fixedField (H : ClosedSubgroup (K ≃ₐ[k] K)) :
  (IntermediateField.fixedField H).fixingSubgroup = H.1 := sorry
--by_contra and find a nhds (subgroup smul) and use 22.2

def intermediateFieldEquivClosedSubgroup [IsGalois k K] :
  IntermediateField k K ≃o ClosedSubgroup (K ≃ₐ[k] K)ᵒᵈ := sorry

end InfiniteGalois
