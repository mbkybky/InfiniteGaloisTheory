/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.KrullTopology
import InfiniteGaloisTheory.ProFinite.Basic
import InfiniteGaloisTheory.MissingLemmas.Galois

set_option linter.unusedTactic false

open CategoryTheory Topology

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]

def FiniteIntermediateField := {L : (IntermediateField k K) | (FiniteDimensional k L) ∧ (IsGalois k L)}

instance : PartialOrder (FiniteIntermediateField k K) := inferInstance

def Gal_inclusion {L₁ L₂ : (FiniteIntermediateField k K)ᵒᵖ} (le : L₂.unop ≤ L₁.unop): (L₁.unop ≃ₐ[k] L₁.unop) →* (L₂.unop ≃ₐ[k] L₂.unop) := by sorry

/-by
    let coeL₁ := ((fun a ↦ ↑a) (L₁.unop))
    letI : IsGalois k coeL₁ := sorry
    letI : FiniteDimensional k coeL₁ := sorry
    set coeG := coeL₁ ≃ₐ[k] coeL₁
    let coeL₂ := (IntermediateField.restrict h.1.1.1)
    letI : IsGalois k coeL₂ := sorry
    letI : IsGalois k ↥coeL₂ := sorry
    let H : Subgroup (coeL₁ ≃ₐ[k] coeL₁) := coeL₂.fixingSubgroup
    let f1 : (L₁.unop ≃ₐ[k] L₁.unop) ≃* (coeL₁ ≃ₐ[k] coeL₁) := MulEquiv.refl (L₁.unop ≃ₐ[k] L₁.unop)
    letI : H.Normal := IsGalois.fixingSubgroup_Normal_of_Galois coeL₂
    let f2 := QuotientGroup.mk' H
    let f3 := (IsGalois.normal_aut_equiv_quotient H)
    have eq : IntermediateField.fixedField H = coeL₂ := sorry
    let f4 : ((IntermediateField.fixedField H) ≃ₐ[k] (IntermediateField.fixedField H)) ≃* (coeL₂ ≃ₐ[k] coeL₂) :=
      sorry
    let f5 : (coeL₂ ≃ₐ[k] coeL₂) ≃* (L₂.unop ≃ₐ[k] L₂.unop) := sorry
    #check (f5.toMonoidHom.comp f4.toMonoidHom).comp f3.symm.toMonoidHom
    sorry-/

/-noncomputable example : (FiniteIntermediateField k K)ᵒᵖ ⥤ FiniteGrp.{u} where
  obj := fun L => {
    carrier := Grp.of (L.unop ≃ₐ[k] L.unop)
    isFinite :=
      letI : FiniteDimensional k L.unop := L.1.2.1
      AlgEquiv.fintype k L.unop
  }
  map := fun {L₁ L₂} h => Gal_inclusion k K h.1.1.1-/

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
