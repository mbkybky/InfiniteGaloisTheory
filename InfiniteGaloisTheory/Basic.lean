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

noncomputable def Gal_inclusion {L₁ L₂ : (FiniteIntermediateField k K)ᵒᵖ} (le : L₂.unop ≤ L₁.unop): (L₁.unop ≃ₐ[k] L₁.unop) →* (L₂.unop ≃ₐ[k] L₂.unop) :=
  letI := L₂.1.2.2
  letI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion le)
  letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  AlgEquiv.restrictNormalHom (F := k) (K₁ := L₁.unop) L₂.unop

/-noncomputable example : (FiniteIntermediateField k K)ᵒᵖ ⥤ FiniteGrp.{u} where
  obj := fun L => {
    carrier := Grp.of (L.unop ≃ₐ[k] L.unop)
    isFinite :=
      letI : FiniteDimensional k L.unop := L.1.2.1
      AlgEquiv.fintype k L.unop
  }
  map := fun {L₁ L₂} h => Gal_inclusion k K h.1.1.1-/

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
