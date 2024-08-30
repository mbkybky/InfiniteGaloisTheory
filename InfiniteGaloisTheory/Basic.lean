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

theorem AlgEquiv.restrictNormalHom_id (F K : Type*)
    [Field F] [Field K] [Algebra F K] [Normal F K] :
    AlgEquiv.restrictNormalHom (F := F) (K₁ := K) K = MonoidHom.id (K ≃ₐ[F] K) := by
  ext f x
  dsimp [restrictNormalHom]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp

theorem IsScalarTower.algEquivRestrictNormalHom_eq (F K₁ K₂ K₃ : Type*)
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] :
    AlgEquiv.restrictNormalHom (F := F) (K₁ := K₃) K₁ =
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₂) K₁).comp
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₃) K₂) := by
  ext f x
  dsimp [AlgEquiv.restrictNormalHom]
  apply (algebraMap K₁ K₃).injective
  conv_rhs => rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormal_commutes, RingHom.coe_comp, Function.comp_apply,
    EmbeddingLike.apply_eq_iff_eq]
  exact IsScalarTower.algebraMap_apply K₁ K₂ K₃ x

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
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom (F := k) (K₁ := L₁.unop) L₂.unop)

lemma finGalMap.map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGalMap (𝟙 L)) = 𝟙 L.unop.finGal :=
  AlgEquiv.restrictNormalHom_id _ _

lemma finGalMap.map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) : finGalMap (f ≫ g) = finGalMap f ≫ finGalMap g := by
  suffices h : ∀ (L₁ L₂ L₃ : FiniteGaloisIntermediateField k K) (hf : L₂ ≤ L₁) (hg : L₃ ≤ L₂),
      finGalMap (Opposite.op hf.hom ≫ Opposite.op hg.hom) = finGalMap (Opposite.op hf.hom) ≫ finGalMap (Opposite.op hg.hom) by
    exact h _ _ _ _ _
  intro L₁ L₂ L₃ hf hg
  letI : Algebra L₃ L₂ := RingHom.toAlgebra (Subsemiring.inclusion hg)
  letI : Algebra L₂ L₁ := RingHom.toAlgebra (Subsemiring.inclusion hf)
  letI : Algebra L₃ L₁ := RingHom.toAlgebra (Subsemiring.inclusion (hg.trans hf))
  haveI : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  apply IsScalarTower.algEquivRestrictNormalHom_eq k L₃ L₂ L₁

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

noncomputable def HomtoLimit : (K ≃ₐ[k] K) →*
    ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)) where
  toFun σ := ⟨fun L => (AlgEquiv.restrictNormalHom L.unop) σ, by
    intro L₁ L₂ π
    unfold finGalFunctor
    dsimp
    unfold finGalMap
    symm
    letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom π.1)
    letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    letI : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    rw [IsScalarTower.algEquivRestrictNormalHom_eq k L₂.unop L₁.unop K]
    rfl ⟩
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
