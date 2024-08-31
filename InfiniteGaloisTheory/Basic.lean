/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure
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

* `union_eq_univ` : In `K/k`, the union of all the `FiniteGaloisIntermediateField` is equal to `K`,
  Furthermore, there is also a `FiniteGaloisIntermediateField` containing any tuple `(x,y)`

* `HomtoLimit` : Based on the canonical projection from `Gal(K/k)` to any `Gal(L/k)`
  where `L` is `FiniteGaloisIntermediateField`, it can be easily verified that
  the projections are compatible with the morphisms on `FiniteGaloisIntermediateField`
  (ordered by inverse inclusion)

* `ContinuousMulEquiv` : Three main parts :
  1. Injectivity : For two element of `Gal(K/k)` must be different at some `x`, as `union_eq_univ`
     mentioned above, the coordinate at the normal closure of simple extension of `x`
     (can be easily verified finite and galois) is different,
     thus differnt in the subgroup of the product space.
  2. Surjectivity : It is basically constructing an element of `Gal(K/k)`
    by binding the compatible elements of `Gal(L/k)` where `L` is `FiniteGaloisIntermediateField`
    A lemma is needed : for an element `g` in `lim Gal(L/k)` ordered by inverse inclusion,
    any two `FiniteGaloisIntermediateField` `L₁ L₂` containing an element`x` of `K`,
    `g` in the coordinate of `L₁` and `L₂` maps `x` to the same element of `K`.
    Then by defining the image of `g` in `Gal(K/k)` pointwise by arbitrarily choose an
    `FiniteGaloisIntermediateField` `L` containing `x` and use the image of
    `g` in the coordinate of `L` acting on `x`. By using the lemma repeatedly, we can get an AlgHom.
    The by the bijectivity, it can be made into an element of `Gal(K/k)`
  3. Two-sided continuity :

* `Profinite`

# implementation note

This file compiles very slowly, mainly because the two composition of restriction as a composition
of an inverse function of an AlgEquiv composite with another AlgEquiv. Thanks to Yuyang Zhao for
modifying the proofs.

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

theorem IsScalarTower.algEquivRestrictNormalHom_apply (F K₁ K₂ : Type*) {K₃ : Type*}
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] (f : K₃ ≃ₐ[F] K₃) :
    AlgEquiv.restrictNormalHom K₁ f =
      (AlgEquiv.restrictNormalHom K₁) (AlgEquiv.restrictNormalHom K₂ f) := by
  rw [IsScalarTower.algEquivRestrictNormalHom_eq F K₁ K₂ K₃, MonoidHom.comp_apply]

open CategoryTheory Topology Opposite
open scoped IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

@[ext]
structure FiniteGaloisIntermediateField where
  val : IntermediateField k K
  [finiteDimensional : FiniteDimensional k val]
  [isGalois : IsGalois k val]

namespace FiniteGaloisIntermediateField

attribute [coe] val

instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := val

instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.val

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L.val :=
  L.finiteDimensional

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L.val :=
  L.isGalois

variable {k K}

lemma val_injective : Function.Injective (val (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa using eq

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊔ L₂) := {}

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₁] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion inf_le_left).toLinearMap
    (IntermediateField.inclusion inf_le_left).injective

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₂] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion inf_le_right).toLinearMap
    (IntermediateField.inclusion inf_le_right).injective

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₁] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_left)

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₂] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_right)

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊓ L₂) := {}

instance : Sup (FiniteGaloisIntermediateField k K) where
  sup L₁ L₂ := .mk <| L₁.val ⊔ L₂.val

instance : Inf (FiniteGaloisIntermediateField k K) where
  inf L₁ L₂ := .mk <| L₁.val ⊓ L₂.val

instance : Lattice (FiniteGaloisIntermediateField k K) :=
  val_injective.lattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

-- instance : ConditionallyCompleteLattice (FiniteGaloisIntermediateField k K)

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
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  letI : Algebra L₃ L₂ := RingHom.toAlgebra (Subsemiring.inclusion g.unop.le)
  letI : Algebra L₂ L₁ := RingHom.toAlgebra (Subsemiring.inclusion f.unop.le)
  letI : Algebra L₃ L₁ := RingHom.toAlgebra (Subsemiring.inclusion (g.unop.le.trans f.unop.le))
  haveI : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  apply IsScalarTower.algEquivRestrictNormalHom_eq k L₃ L₂ L₁

def finGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGal
  map := finGalMap
  map_id := finGalMap.map_id
  map_comp := finGalMap.map_comp

variable (k) in
def adjoin [IsGalois k K] (s : Set K) [Finite s] : FiniteGaloisIntermediateField k K where
  val := normalClosure k (IntermediateField.adjoin k (s : Set K)) K
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) := by
      have hS : ∀ z ∈ s, IsIntegral k z := fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
      exact IntermediateField.finiteDimensional_adjoin hS
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K

variable (k) in
lemma subset_adjoin [IsGalois k K] (s : Set K) [Finite s] :
    s ⊆ (adjoin k s).val := by
  intro x hx
  apply IntermediateField.le_normalClosure
  unfold IntermediateField.adjoin
  simp only [Set.union_insert, Set.union_singleton, IntermediateField.mem_mk,
    Subring.mem_toSubsemiring, Subfield.mem_toSubring]
  apply Subfield.subset_closure
  simp [hx]

noncomputable def homtoLimit : (K ≃ₐ[k] K) →*
    ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)) where
  toFun σ :=
  { val := fun L => (AlgEquiv.restrictNormalHom L.unop) σ
    property := fun L₁ L₂ π ↦ by
      dsimp [finGalFunctor, finGalMap]
      letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion π.1.le)
      letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      letI : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      apply (IsScalarTower.algEquivRestrictNormalHom_apply k L₂.unop L₁.unop σ).symm }
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl

lemma restrict_eq (σ : K ≃ₐ[k] K) (x : K) (Lx : FiniteGaloisIntermediateField k K) (hLx : x ∈ Lx.val) :
    σ x = (AlgEquiv.restrictNormalHom Lx σ) ⟨x, hLx⟩ := by
  change σ x = ((AlgEquiv.restrictNormal σ Lx) ⟨x, hLx⟩).1
  have := AlgEquiv.restrictNormal_commutes σ Lx ⟨x, hLx⟩
  convert this
  exact id this.symm

theorem homtoLimit_inj [IsGalois k K] : Function.Injective (homtoLimit (k := k) (K := K)) := by
  intro σ₁ σ₂ heq
  ext x
  have : homtoLimit.toFun σ₁ = homtoLimit.toFun σ₂ := heq
  unfold homtoLimit at this
  push_cast at this
  apply_fun Subtype.val at this
  dsimp at this
  have : (AlgEquiv.restrictNormalHom (adjoin k {x}) σ₁ ⟨x, subset_adjoin _ _ (by simp)⟩).val =
      (AlgEquiv.restrictNormalHom (adjoin k {x}) σ₂ ⟨x, subset_adjoin _ _ (by simp)⟩).val :=
    congr($this _ _)
  convert this
  all_goals apply restrict_eq

lemma homtoLimit_lift'
    (g : ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)))
    (x : K) {L : FiniteGaloisIntermediateField k K} (hL : x ∈ L.val)
    {L' : FiniteGaloisIntermediateField k K} (hL' : x ∈ L'.val) (h : L ⟶ L') :
    ((g.1 (op L)).1 ⟨x, hL⟩).1 = ((g.1 (op L')).1 ⟨x, hL'⟩).1 := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  letI : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h.le)
  letI : IsScalarTower k L L' :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have := g.2 h.op
  rw [←this]
  unfold finGalFunctor
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  dsimp [finGalMap, AlgEquiv.restrictNormalHom]
  change (AlgEquiv.restrictNormal (g.1 (op (mk L'))) L ⟨x, hL⟩).1 =
    ((g.1 (op (mk L'))).1 ⟨x, hL'⟩).1
  have comm := AlgEquiv.restrictNormal_commutes (g.1 (op (mk L'))) L ⟨x, hL⟩
  have : algebraMap L L' ⟨x, hL⟩ = ⟨x, hL'⟩ := by rfl
  rw [this] at comm
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [←comm]
  rfl

lemma homtoLimit_lift [IsGalois k K]
  (g : ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)))
  (x : K) {L : FiniteGaloisIntermediateField k K} (hL : x ∈ L.val) :
    (g.1 (op L)).1 ⟨x, hL⟩ =
    ((g.1 (op (adjoin k {x}))).1 ⟨x, subset_adjoin _ _ (by simp)⟩).1
      := by
    let Lx := adjoin k {x}
    have hLx : x ∈ Lx.val := subset_adjoin _ _ (by simp)
    change ((g.1 (op L)).1 ⟨x, hL⟩).1 = ((g.1 (op Lx)).1 ⟨x, hLx⟩).1
    let Lm'' := L.1 ⊔ Lx.1
    letI : FiniteDimensional k Lm'' := IntermediateField.finiteDimensional_sup L.1 Lx.1
    let Lm' := normalClosure k Lm'' K
    let Lm : FiniteGaloisIntermediateField k K := mk Lm'
    have Lm''_le : Lm'' ≤ Lm.1 := IntermediateField.le_normalClosure Lm''
    have L_le : L.val ≤ Lm.val := le_trans (SemilatticeSup.le_sup_left L.1 Lx.1) Lm''_le
    have Lx_le : Lx.val ≤ Lm.val := le_trans (SemilatticeSup.le_sup_right L.1 Lx.1) Lm''_le
    have trans1 : ((g.1 (op L)).1 ⟨x, hL⟩).1 = ((g.1 (op Lm)).1 ⟨x, (L_le hL)⟩).1 :=
      homtoLimit_lift' g x hL (L_le hL) L_le.hom
    have trans2 : ((g.1 (op Lx)).1 ⟨x, hLx⟩).1 =
      ((g.1 (op Lm)).1 ⟨x, L_le hL⟩).1 := homtoLimit_lift' g x hLx (L_le hL) Lx_le.hom
    rw [trans1, trans2]

def bot : FiniteGaloisIntermediateField k K := ⟨⊥⟩

instance : Algebra k (bot (k := k) (K := K)) := bot.val.algebra'

theorem homtoLimit_surj [IsGalois k K] : Function.Surjective (homtoLimit (k := k) (K := K)) := by
  intro g
  let σ' : K →ₐ[k] K := {
    toFun := fun x => ((g.1 (op (adjoin k {x}))).1 ⟨x, subset_adjoin _ _ (by simp)⟩).1
    map_one' := by
      dsimp
      have h1 : 1 ∈ (bot (k := k) (K := K)).val := by exact bot.val.one_mem'
      have := homtoLimit_lift g 1 h1
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at this
      rw [←this]
      have : ((g.1 (op bot)).1 ⟨1, h1⟩) = 1 := by
        simp only [AlgEquiv.toEquiv_eq_coe,
          EquivLike.coe_coe, MulEquivClass.map_eq_one_iff]
        rfl
      dsimp at this
      rw [this]
      rfl
    map_mul' := fun x y => by
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        IntermediateField.coe_toSubalgebra, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      let L := adjoin k {x, y}
      have hxL : x ∈ L.val := subset_adjoin _ _ (by simp)
      have hyL : y ∈ L.val := subset_adjoin _ _ (by simp)
      have hxyL : x * y ∈ L.val := mul_mem hxL hyL
      have hx := homtoLimit_lift g x hxL
      have hy := homtoLimit_lift g y hyL
      have hxy := homtoLimit_lift g (x * y) hxyL
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at hx hy hxy
      rw [← hx, ← hy, ← hxy]
      have : (⟨x * y, hxyL⟩ : L) = (⟨x, hxL⟩ : L) * (⟨y, hyL⟩ : L) := rfl
      rw [this, map_mul]
      rfl
    map_zero' := by
      dsimp
      have h0 : 0 ∈ (bot (k := k) (K := K)).val := zero_mem _
      have := homtoLimit_lift g 0 h0
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at this
      rw [←this]
      have : ((g.1 (op bot)).1 ⟨0,h0⟩) = 0 := by
        simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AddEquivClass.map_eq_zero_iff]
        rfl
      dsimp at this
      rw [this]
      rfl
    map_add' := fun x y => by
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        IntermediateField.coe_toSubalgebra, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      let L := adjoin k {x, y}
      have hxL : x ∈ L.val := subset_adjoin _ _ (by simp)
      have hyL : y ∈ L.val := subset_adjoin _ _ (by simp)
      have hx := homtoLimit_lift g x hxL
      have hy := homtoLimit_lift g y hyL
      have hxy := homtoLimit_lift g (x + y) (add_mem hxL hyL)
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at hx hy hxy
      rw [← hx, ← hy, ← hxy]
      rw [← AddMemClass.mk_add_mk _ _ _ hxL hyL, map_add]
      rfl
    commutes' := fun z => by
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        IntermediateField.coe_toSubalgebra, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      have hzbot : algebraMap k K z ∈ (bot (k := k) (K := K)).val := bot.val.algebraMap_mem z
      have hz := homtoLimit_lift g ((algebraMap k K) z) hzbot
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at hz
      rw [← hz]
      have := (g.1 (op bot)).commutes' z
      exact congrArg Subtype.val this
  }
  have := Algebra.IsAlgebraic.algHom_bijective σ'
  let σ := AlgEquiv.ofBijective σ' this
  use σ
  apply Subtype.val_injective
  ext L
  unfold_let σ
  unfold homtoLimit AlgEquiv.restrictNormalHom
  simp only [MonoidHom.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  unfold AlgEquiv.restrictNormal
  have : (AlgEquiv.ofBijective σ' this).toAlgHom = σ' := rfl
  simp_rw [this]
  apply AlgEquiv.ext
  intro x
  have : (σ'.restrictNormal' L.unop) x = σ' x.1 := by
    unfold AlgHom.restrictNormal'
    simp only [AlgEquiv.coe_ofBijective]
    have := AlgHom.restrictNormal_commutes σ' L.unop x
    convert this
  apply Subtype.val_injective
  rw [this]
  change σ' x.1 = ((g.1 L).1 x).1
  simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
    IntermediateField.coe_toSubalgebra, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  symm
  apply homtoLimit_lift

noncomputable def  MulEquivtoLimit [IsGalois k K] : (K ≃ₐ[k] K) ≃*
    ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)) :=
  MulEquiv.ofBijective homtoLimit ⟨homtoLimit_inj, homtoLimit_surj⟩

#check TopologicalSpace.IsTopologicalBasis.continuous_iff

lemma LimtoGalContinuous [IsGalois k K] : Continuous
  (MulEquivtoLimit (k := k) (K := K)).symm := by
  apply continuous_of_continuousAt_one
  apply continuousAt_def.mpr
  simp only [map_one, GroupFilterBasis.nhds_one_eq]
  intro H hH
  rcases hH with ⟨O,hO1,hO2⟩
  rcases hO1 with ⟨gp,hgp1,hgp2⟩
  have op : IsOpen (⇑MulEquivtoLimit.symm ⁻¹' O) := by

    sorry
  have sub : (⇑MulEquivtoLimit.symm ⁻¹' O) ⊆ (⇑MulEquivtoLimit.symm ⁻¹' H) := fun ⦃a⦄ => fun a ↦ hO2 a
  apply mem_nhds_iff.mpr
  use (⇑MulEquivtoLimit.symm ⁻¹' O)
  simp only [sub, op, Set.mem_preimage, map_one, true_and]
  rw [←hgp2]
  exact gp.one_mem'

instance [IsGalois k K] : CompactSpace (ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K))) :=
  inferInstance

instance [IsGalois k K] : Algebra.IsIntegral k K := inferInstance

instance [IsGalois k K] : T2Space (K ≃ₐ[k] K) := krullTopology_t2

def LimtoGalHomeo [IsGalois k K] : (ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K))) ≃ₜ (K ≃ₐ[k] K)
  := Continuous.homeoOfEquivCompactToT2 LimtoGalContinuous

noncomputable def  ContinuousMulEquivtoLimit [IsGalois k K] : ContinuousMulEquiv (K ≃ₐ[k] K)
  (ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K))) := {
    MulEquivtoLimit (k := k) (K := K) with
    continuous_toFun := LimtoGalHomeo.continuous_invFun
    continuous_invFun := LimtoGalHomeo.continuous_toFun
  }

end FiniteGaloisIntermediateField

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
