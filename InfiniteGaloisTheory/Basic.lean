/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan, Yuyang Zhao
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

In `K/k`

* `FiniteGaloisIntermediateField` : The Finite Galois IntermediateField of `K/k`

* `finGal L` : For a `FiniteGaloisIntermediateField` `L`, make `Gal(L/k)` into a FiniteGrp

* `finGalMap L₁ ⟶ L₂` : For `FiniteGaloisIntermediateField` `L₁ L₂` ordered by inverse inclusion,
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGalFunctor` : Mapping `FiniteGaloisIntermediateField` ordered by inverse inclusion to its
  corresponding Galois Group as FiniteGrp

* `union`

* `Hom Gal → lim`

* `continuousMulEquiv`

* `Profinite`

# implementation note

This file compiles very slowly, mainly because the two composition of restriction as a composition
of an inverse function of an AlgEquiv composite with another AlgEquiv

-/

suppress_compilation

open CategoryTheory Topology

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] -- [IsGalois k K]

@[ext]
structure FiniteGaloisIntermediateField extends IntermediateField k K where
  [fin_dim : FiniteDimensional k toIntermediateField]
  [is_gal : IsGalois k toIntermediateField]

namespace FiniteGaloisIntermediateField

instance : SetLike (FiniteGaloisIntermediateField k K) K where
  coe L := L.carrier
  coe_injective' := by rintro ⟨⟩ ⟨⟩; simp

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L :=
  L.fin_dim

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L :=
  L.is_gal

variable {k K}

lemma injective_toIntermediateField : Function.Injective
    fun (L : FiniteGaloisIntermediateField k K) => L.toIntermediateField := by
  intro L1 L2 eq
  dsimp at eq
  ext : 1
  show L1.toIntermediateField.carrier = L2.toIntermediateField.carrier
  rw [eq]

instance : PartialOrder (FiniteGaloisIntermediateField k K) :=
  PartialOrder.lift FiniteGaloisIntermediateField.toIntermediateField injective_toIntermediateField

def finGal (L : FiniteGaloisIntermediateField k K) : FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

def finGalMap
    {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) :
    L₁.unop.finGal ⟶ L₂.unop.finGal :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
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

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 50000 in
lemma finGalMap.map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) : finGalMap (f ≫ g) = finGalMap f ≫ finGalMap g := by
  unfold finGalMap
  letI : Algebra L₃.unop L₂.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom g.1)
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom f.1)
  letI : Algebra L₃.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom (f ≫ g).1)
  haveI : IsScalarTower k L₃.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower L₃.unop L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃.unop L₂.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)


  refine DFunLike.ext _ _ fun (σ : AlgEquiv _ _ _) => ?_
  change AlgEquiv.restrictNormal σ L₃.unop =
    AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ L₂.unop) L₃.unop
  refine AlgEquiv.ext fun x => ?_
  dsimp only [AlgEquiv.restrictNormal, AlgHom.restrictNormal', AlgEquiv.toAlgHom_eq_coe,
    AlgHom.restrictNormal, AlgHom.restrictNormalAux, AlgHom.coe_coe, AlgEquiv.coe_ofBijective,
    AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply]
  apply_fun AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₁.unop)
  simp only [AlgEquiv.apply_symm_apply]
  have eq (x) : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₁.unop)) x =
    ⟨⟨x, leOfHom (f ≫ g).1 x.2⟩, by aesop⟩ := rfl
  conv_rhs => rw [eq]
  ext : 2
  dsimp only
  symm
  have eq x : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)) x =
    ⟨⟨x, leOfHom f.1 x.2⟩, by aesop⟩ := rfl
  simp_rw [eq]
  have eq x : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₂.unop)) x =
    ⟨⟨x, leOfHom g.1 x.2⟩, by aesop⟩ := rfl
  simp_rw [eq]

  dsimp only [SetLike.coe_sort_coe, IsScalarTower.coe_toAlgHom', id_eq, eq_mpr_eq_cast, cast_eq,
    eq_mp_eq_cast]
  generalize_proofs h1 h2 h3 h4 h5
  change ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₂.unop)).symm
    ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)).symm
      ⟨σ ⟨x, leOfHom (f ≫ g).1 x.2⟩, h4⟩, h5⟩).1 = _
  suffices eq : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₂.unop)).symm
    ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)).symm
      ⟨σ ⟨x, leOfHom (f ≫ g).1 x.2⟩, h4⟩, h5⟩ =
    ⟨σ ⟨x, _⟩, by
      simp only [AlgHom.mem_range, IsScalarTower.coe_toAlgHom', Subtype.exists] at h5
      obtain ⟨a, ha, eq⟩ := h5
      apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)) at eq
      simp only [AlgEquiv.apply_symm_apply] at eq
      rw [Subtype.ext_iff] at eq
      simp only at eq
      erw [← eq]
      exact ha⟩ by
    rw [eq]
    rfl

  apply_fun AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₃.unop L₂.unop)
  simp only [AlgEquiv.apply_symm_apply]
  ext : 1
  apply_fun AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)
  simp only [AlgEquiv.apply_symm_apply]
  rfl

def finGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp.{u} where
  obj L := L.unop.finGal
  map := finGalMap
  map_id := finGalMap.map_id
  map_comp := finGalMap.map_comp

lemma union_eq_univ'' (x y : K) [IsGalois k K] : ∃ L : (FiniteGaloisIntermediateField k K),
    x ∈ L.carrier ∧ y ∈ L.carrier := by
  let L' := normalClosure k (IntermediateField.adjoin k ({x,y} : Set K)) K
  letI : FiniteDimensional k (IntermediateField.adjoin k ({x,y} : Set K)) := by
    have hS : ∀ z ∈ ({x,y} : Set K), IsIntegral k z := fun z _ =>
      IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    exact IntermediateField.finiteDimensional_adjoin hS
  let L : (FiniteGaloisIntermediateField k K) := {
    L' with
    fin_dim := normalClosure.is_finiteDimensional k (IntermediateField.adjoin k ({x,y} : Set K)) K
    is_gal := IsGalois.normalClosure k (IntermediateField.adjoin k ({x,y} : Set K)) K
  }
  use L
  constructor
  all_goals apply IntermediateField.le_normalClosure
  all_goals unfold IntermediateField.adjoin
  all_goals simp only [Set.union_insert, Set.union_singleton, IntermediateField.mem_mk,
      Subring.mem_toSubsemiring, Subfield.mem_toSubring]
  all_goals apply Subfield.subset_closure
  · exact (Set.mem_insert x (insert y (Set.range ⇑(algebraMap k K))))
  · apply Set.subset_insert
    exact Set.mem_insert y (Set.range ⇑(algebraMap k K))

lemma union_eq_univ' (x : K) [IsGalois k K] : ∃ L : (FiniteGaloisIntermediateField k K),
    x ∈ L.carrier := by
  rcases (union_eq_univ'' (k := k) (K := K) x 1) with ⟨L,hL⟩
  exact ⟨L,hL.1⟩

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 50000 in
noncomputable def HomtoLimit : (K ≃ₐ[k] K) →*
    ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)) where
  toFun σ := ⟨fun L => (AlgEquiv.restrictNormalHom L.unop) σ,
    by
    intro L₁ L₂ π
    unfold finGalFunctor
    dsimp
    unfold finGalMap
    symm
    letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom π.1)
    letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    change AlgEquiv.restrictNormal σ L₂.unop =
    AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ L₁.unop) L₂.unop
    refine AlgEquiv.ext fun x => ?_
    dsimp only [AlgEquiv.restrictNormal, AlgHom.restrictNormal', AlgEquiv.toAlgHom_eq_coe,
    AlgHom.restrictNormal, AlgHom.restrictNormalAux, AlgHom.coe_coe, AlgEquiv.coe_ofBijective,
    AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply]
    apply_fun
      (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k (↥(L₂.unop).toIntermediateField) K))
    simp only [AlgEquiv.apply_symm_apply]
    have eq (x) : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop K)) x =
      ⟨x, by aesop⟩ := rfl
    conv_rhs => rw [eq]
    ext : 2
    dsimp only
    symm
    have eq (x) : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₁.unop K)) x =
        ⟨x, by aesop⟩ := rfl
    simp_rw [eq]
    have eq (x) : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)) x =
        ⟨⟨x, leOfHom π.1 x.2⟩, by aesop⟩ := rfl
    simp_rw [eq]

    dsimp only [SetLike.coe_sort_coe, IsScalarTower.coe_toAlgHom', id_eq, eq_mpr_eq_cast, cast_eq,
      eq_mp_eq_cast]
    generalize_proofs h1 h2 h3 h4 h5
    change ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)).symm
      ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₁.unop K)).symm ⟨σ x, h4⟩, h5⟩).1 = _
    suffices eq : (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop)).symm
      ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₁.unop K)).symm
        ⟨σ x, h4⟩, h5⟩ = ⟨σ x, by
        simp only [AlgHom.mem_range, IsScalarTower.coe_toAlgHom', Subtype.exists] at h5
        obtain ⟨a, ha, eq⟩ := h5
        apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₁.unop K)) at eq
        simp only [AlgEquiv.apply_symm_apply] at eq
        rw [Subtype.ext_iff] at eq
        simp only at eq
        erw [← eq]
        exact ha⟩ by
      rw [eq]
      rfl
    apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₂.unop L₁.unop))
    simp only [AlgEquiv.apply_symm_apply]
    ext : 1
    apply_fun (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L₁.unop K))
    simp only [AlgEquiv.apply_symm_apply]
    rfl⟩
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl

theorem HomtoLimit_inj : Function.Injective (HomtoLimit (k := k) (K := K)) := by sorry

#check algEquivEquivAlgHom

theorem HomtoLimit_surj : Function.Surjective (HomtoLimit (k := k) (K := K)) := by sorry

end FiniteGaloisIntermediateField

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
