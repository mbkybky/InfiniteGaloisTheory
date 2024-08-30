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

/-!

# Galois Group as a Profinite Group

In this file, we ....

# Main definitions and results

* `finGal L` : if `L`


-/

-- set_option linter.unusedTactic false

open CategoryTheory Topology

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] -- [IsGalois k K]

@[ext]
structure FiniteGaloisIntermediateField extends IntermediateField k K where
  fin_dim : FiniteDimensional k toIntermediateField
  is_gal : IsGalois k toIntermediateField

namespace FiniteGaloisIntermediateField

instance : CoeSort (FiniteGaloisIntermediateField k K) (Type u) where
  coe L := L.toIntermediateField

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L :=
  L.fin_dim

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L :=
  L.is_gal

variable {k K}

lemma injective_toIntermediateField : Function.Injective fun (L : FiniteGaloisIntermediateField k K) => L.toIntermediateField := by
  intro L1 L2 eq
  dsimp at eq
  ext : 1
  show L1.toIntermediateField.carrier = L2.toIntermediateField.carrier
  rw [eq]

instance : PartialOrder (FiniteGaloisIntermediateField k K) :=
  PartialOrder.lift FiniteGaloisIntermediateField.toIntermediateField injective_toIntermediateField

noncomputable def finGal (L : (FiniteGaloisIntermediateField k K)) : FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

noncomputable def finGalMap
    {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) :
    (L₁.unop.finGal) ⟶ (L₂.unop.finGal) :=
  letI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  AlgEquiv.restrictNormalHom (F := k) (K₁ := L₁.unop) L₂.unop

lemma finGalMap.map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGalMap (𝟙 L)) = 𝟙 (L.unop.finGal) := by
  unfold finGalMap AlgEquiv.restrictNormalHom
  congr
  ext x y : 2
  simp only [AlgEquiv.restrictNormal, AlgHom.restrictNormal', AlgHom.restrictNormal,
    AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ofBijective, AlgHom.coe_comp, AlgHom.coe_coe,
    Function.comp_apply]
  apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k (L.unop) (L.unop)))
  simp only [MonoidHom.mk'_apply, AlgEquiv.coe_ofBijective, AlgHom.coe_comp, AlgHom.coe_coe,
    Function.comp_apply, AlgEquiv.apply_symm_apply, types_id_apply]
  ext
  simp only [AlgHom.restrictNormalAux, AlgHom.coe_coe, AlgEquiv.ofInjectiveField, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.ofInjective_apply,
    IsScalarTower.coe_toAlgHom', Algebra.id.map_eq_id, RingHom.id_apply]

lemma finGalMap.map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) : finGalMap (f ≫ g) = (finGalMap f) ≫ (finGalMap g) := by

  sorry

noncomputable def finGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp.{u} where
  obj L := L.unop.finGal
  map := finGalMap
  map_id := finGalMap.map_id
  map_comp := finGalMap.map_comp



end FiniteGaloisIntermediateField


/-
-- def FiniteGaloisIntermediateField := {L : (IntermediateField k K) | (FiniteDimensional k L) ∧ (IsGalois k L)}

-- instance : PartialOrder (FiniteGaloisIntermediateField k K) := inferInstance

variable {k K}
open Opposite
noncomputable def finGal (L : (FiniteGaloisIntermediateField k K)) : FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

noncomputable def finGalMap
    {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) :
    (finGal $ op L₁) ⟶ (finGal $ op L₂) :=
  letI := L₂.1.2.2
  letI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion le.1.1.1)
  letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  AlgEquiv.restrictNormalHom (F := k) (K₁ := L₁.unop) L₂.unop

lemma finGalMap.map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGalMap (𝟙 L)) = 𝟙 (finGal L) := by

  unfold finGalMap AlgEquiv.restrictNormalHom
  congr
  ext x y : 2
  simp only [AlgEquiv.restrictNormal, AlgHom.restrictNormal', AlgHom.restrictNormal,
    AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ofBijective, AlgHom.coe_comp, AlgHom.coe_coe,
    Function.comp_apply]
  apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k (L.unop) (L.unop)))
  simp only [MonoidHom.mk'_apply, AlgEquiv.coe_ofBijective, AlgHom.coe_comp, AlgHom.coe_coe,
    Function.comp_apply, AlgEquiv.apply_symm_apply, types_id_apply]
  ext
  simp only [AlgHom.restrictNormalAux, AlgHom.coe_coe, AlgEquiv.ofInjectiveField, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.ofInjective_apply,
    IsScalarTower.coe_toAlgHom', Algebra.id.map_eq_id, RingHom.id_apply]

noncomputable example : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp.{u} where
  obj := finGal
  map := finGalMap
  map_id := finGalMap.map_id

  map_comp := sorry
  /-obj := fun L => {
    carrier := Grp.of (L.unop ≃ₐ[k] L.unop)
    isFinite :=
      letI : FiniteDimensional k L.unop := L.1.2.1
      AlgEquiv.fintype k L.unop
  }
  map := fun {L₁ L₂} h => finGalMap k K h.1.1.1-/

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
-/
