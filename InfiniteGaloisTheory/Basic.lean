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

* `ContinuousMulEquiv` : A ContinuousMulEquiv from `Gal(K/k)` to `lim Gal(L/k)`
    where `L` is `FiniteGaloisIntermediateField`, ordered by inverse inclusion
  Three main parts :
  1. Injectivity :
    Notice that the coordinate at the normal closure of simple extension of `x`
     is different for two element of `Gal(K/k)` mapping `x` differently.
  2. Surjectivity :
    A lemma is needed (lift): for an element `g` in `lim Gal(L/k)` and any two
    `FiniteGaloisIntermediateField` `L₁ L₂` containing an element`x`,
    `g` in the coordinate of `L₁` and `L₂` maps `x` to the same element of `K`.
    Then by defining the image of `g` in `Gal(K/k)` pointwise in `K` and use the lemma repeatedly,
    we can get an AlgHom. Then by the bijectivity, it can be made into an element of `Gal(K/k)`
  3. Two-sided continuity : Notice that `Gal(K/k)` is T₂,
    `lim Gal(L/k)` ordered by inverse inclusion is Profinite thus compact, we only need the
    continuity from `lim Gal(L/k)` to `Gal(K/k)`, which only need continuity at `1`.
    It can be easily verified by checking the preimage of GroupFilterBasis is open.

* `Profinite`

# implementation note

This file compiles very slowly, mainly because the two composition of restriction as a composition
of an inverse function of an AlgEquiv composite with another AlgEquiv. Thanks to Yuyang Zhao for
modifying the proofs.

-/

suppress_compilation

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

instance IntermediateField.instSMulMemClass : SMulMemClass (IntermediateField F L) F L :=
  ⟨fun _ _ hx ↦ smul_mem _ hx⟩

@[simp]
lemma IntermediateField.normal_map {F L : Type*} [Field F] [Field L] [Algebra F L] [Normal F L]
    (K : IntermediateField F L) (σ : L →ₐ[F] L) :
    normalClosure F (K.map σ) L = normalClosure F K L := by
  have (σ : L ≃ₐ[F] L) : normalClosure F (K.map (σ : L →ₐ[F] L)) L = normalClosure F K L := by
    simp_rw [normalClosure_def'', map_map]
    exact (Equiv.mulRight σ).iSup_congr fun _ ↦ rfl
  simpa using this ((Algebra.IsAlgebraic.algEquivEquivAlgHom _ _).symm σ)

@[simp]
theorem IntermediateField.normalClosure_le_iff_of_normal {k K : Type*} [Field k] [Field K] [Algebra k K]
    {L₁ L₂ : IntermediateField k K} [Normal k L₂] [Normal k K] :
    normalClosure k L₁ K ≤ L₂ ↔ L₁ ≤ L₂ := by
  constructor
  · intro h
    rw [normalClosure_le_iff] at h
    simpa using h L₁.val
  · intro h
    rw [← normalClosure_of_normal L₂]
    exact normalClosure_mono L₁ L₂ h

@[simp]
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
  [to_finiteDimensional : FiniteDimensional k val]
  [to_isGalois : IsGalois k val]

namespace FiniteGaloisIntermediateField

attribute [coe] val

instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := val

instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.val

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L.val :=
  L.to_finiteDimensional

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L.val :=
  L.to_isGalois

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

instance : OrderBot (FiniteGaloisIntermediateField k K) where
  bot := .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

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

variable (k K) in
def finGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGal
  map := finGalMap
  map_id := finGalMap.map_id
  map_comp := finGalMap.map_comp

variable (k) in
def adjoin [IsGalois k K] (s : Set K) [Finite s] : FiniteGaloisIntermediateField k K where
  val := normalClosure k (IntermediateField.adjoin k (s : Set K)) K
  to_finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) := by
      have hS : ∀ z ∈ s, IsIntegral k z := fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
      exact IntermediateField.finiteDimensional_adjoin hS
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  to_isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K

lemma adjoin_val [IsGalois k K] (s : Set K) [Finite s] :
    (FiniteGaloisIntermediateField.adjoin k s).val = normalClosure k (IntermediateField.adjoin k s) K :=
  rfl

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

@[simp]
theorem adjoin_le_iff [IsGalois k K] {s : Set K} [Finite s] {L : FiniteGaloisIntermediateField k K} :
    adjoin k s ≤ L ↔ s ≤ L.val := by
  change normalClosure _ _ _ ≤ L.val ↔ _
  rw [← IntermediateField.adjoin_le_iff, IntermediateField.normalClosure_le_iff_of_normal]

theorem adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} :
    adjoin k {x} ≤ L ↔ x ∈ L.val := by
  simp

@[simp]
theorem adjoin_map [IsGalois k K] (f : K →ₐ[k] K) (s : Set K) [Finite s] :
    adjoin k (f '' s) = adjoin k s := by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map, IntermediateField.normal_map]

@[simp]
theorem adjoin_simple_map [IsGalois k K] (f : K →ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} := by
  simpa using adjoin_map f {x}

@[simp]
theorem adjoin_simple_map' [IsGalois k K] (f : K ≃ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} :=
  adjoin_simple_map (f : K →ₐ[k] K) x

variable (k K) in
@[simps]
noncomputable def homtoLimit : (K ≃ₐ[k] K) →* ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K) where
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

def proj (g : ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K)) (L : FiniteGaloisIntermediateField k K) :
    L.val ≃ₐ[k] L.val :=
  g.val (op L)

@[simp]
lemma finGalFunctor_proj (g : ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K)) {L₁ L₂ : FiniteGaloisIntermediateField k K}
    (h : L₁ ⟶ L₂) : (finGalFunctor k K).map h.op (proj g L₂) = proj g L₁ :=
  g.prop h.op

lemma proj_lift
    (g : ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K))
    (L : FiniteGaloisIntermediateField k K) (x : L)
    (L' : FiniteGaloisIntermediateField k K) (h : L ≤ L') :
    (proj g L x).val = (proj g L' ⟨x, h x.2⟩).val := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  letI : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  letI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGalFunctor_proj g h.hom]
  change (algebraMap L' K (algebraMap L L' (AlgEquiv.restrictNormal (proj g (mk L')) L x))) = _
  rw [AlgEquiv.restrictNormal_commutes (proj g (mk L')) L]
  rfl

lemma proj_lift_adjoin_simple [IsGalois k K]
    (g : ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K))
    (x : K) (y : adjoin k {x})
    (L : FiniteGaloisIntermediateField k K) (h : x ∈ L.val) :
    (proj g (adjoin k {x}) y).val = (proj g L ⟨y, adjoin_simple_le_iff.mpr h y.2⟩).val := by
  rw [proj_lift g _ y]

variable (k K) in
@[simps]
def toAlgHom [IsGalois k K] (g : ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K)) : K →ₐ[k] K where
  toFun x := (proj g (adjoin k {x}) ⟨x, subset_adjoin _ _ (by simp)⟩).1
  map_one' := by
    dsimp
    rw [proj_lift_adjoin_simple g _ _ ⊥ (one_mem _)]
    simp
    rfl
  map_mul' x y := by
    dsimp
    have hx : x ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp)
    have hy : y ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp)
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) hx]
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) hy]
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) (mul_mem hx hy)]
    rw [← MulMemClass.mk_mul_mk, map_mul]
    rfl
  map_zero' := by
    dsimp
    rw [proj_lift_adjoin_simple g _ _ ⊥ (zero_mem _)]
    simp
    rfl
  map_add' x y := by
    dsimp
    have hx : x ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp)
    have hy : y ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp)
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) hx]
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) hy]
    rw [proj_lift_adjoin_simple g _ _ (adjoin k {x, y}) (add_mem hx hy)]
    rw [← AddMemClass.mk_add_mk, map_add]
    rfl
  commutes' z := by
    dsimp
    rw [proj_lift_adjoin_simple g _ _ ⊥ (algebraMap_mem _ z)]
    have := (proj g ⊥).commutes' z
    exact congrArg Subtype.val this

variable (k K) in
noncomputable def mulEquivtoLimit [IsGalois k K] :
    (K ≃ₐ[k] K) ≃* ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K) where
  toFun := homtoLimit k K
  map_mul' := map_mul _
  invFun g := (Algebra.IsAlgebraic.algEquivEquivAlgHom _ _).symm (toAlgHom k K g)
  left_inv := fun f ↦ by
    ext x
    exact AlgEquiv.restrictNormal_commutes f (adjoin k {x}).val ⟨x, _⟩
  right_inv := fun g ↦ by
    apply Subtype.val_injective
    ext L
    change (toAlgHom k K g).restrictNormal' _ = _
    apply AlgEquiv.ext
    intro x
    have : ((toAlgHom k K g).restrictNormal' L.unop) x = (toAlgHom k K g) x.1 := by
      unfold AlgHom.restrictNormal'
      have := AlgHom.restrictNormal_commutes (toAlgHom k K g) L.unop x
      convert this
    apply Subtype.val_injective
    simp_rw [this]
    exact proj_lift_adjoin_simple _ _ _ _ x.2

lemma limtoGalContinuous [IsGalois k K] : Continuous (mulEquivtoLimit k K).symm := by
  apply continuous_of_continuousAt_one
  apply continuousAt_def.mpr
  simp only [map_one, GroupFilterBasis.nhds_one_eq]
  intro H hH
  rcases hH with ⟨O,hO1,hO2⟩
  rcases hO1 with ⟨gp,⟨L,hL1,hL2⟩,hgp⟩
  dsimp at hgp
  have := hL1.out
  set L' : FiniteGaloisIntermediateField k K := {
    val := normalClosure k L K
    to_finiteDimensional := inferInstance
    to_isGalois := inferInstance
  }
  have lecl := IntermediateField.le_normalClosure L
  have : L'.val.fixingSubgroup ≤ L.fixingSubgroup := fun σ h => (mem_fixingSubgroup_iff
    (K ≃ₐ[k] K)).mpr (fun y hy => ((mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp h) y (lecl hy))
  have le1 : (mulEquivtoLimit k K).symm ⁻¹' O ⊆ (mulEquivtoLimit k K).symm ⁻¹' H := fun ⦃a⦄ => fun b => hO2 b
  rw [←hgp, ←hL2] at le1
  have le : (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup ⊆ (mulEquivtoLimit k K).symm ⁻¹' H :=
    fun ⦃a⦄ b ↦ le1 (this b)
  apply mem_nhds_iff.mpr
  use (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup
  constructor
  · exact le
  · constructor
    · have : (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup =
          mulEquivtoLimit k K '' (L'.val.fixingSubgroup : Set (K ≃ₐ[k] K)) := by
        set S := L'.val.fixingSubgroup.carrier
        set f := mulEquivtoLimit k K
        ext σ
        constructor
        all_goals intro h
        · simp only [Set.mem_preimage] at h
          use f.symm σ
          simp only [h, MulEquiv.apply_symm_apply, and_self]
        · rcases h with ⟨σ',h1,h2⟩
          simp [←h2,h1]
      rw [this]
      let fix1 : Set ((L : (FiniteGaloisIntermediateField k K)ᵒᵖ) → (finGalFunctor _ _).obj L) :=
        {x : ((L : (FiniteGaloisIntermediateField k K)ᵒᵖ) → (finGalFunctor _ _).obj L)
          | x (op L') = 1}
      have pre : fix1 = Set.preimage (fun x => x (op L')) {1} := by rfl
      have C : Continuous (fun (x : (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) →
        (finGalFunctor _ _).obj L) ↦ x (op L')) := continuous_apply (op L')
      have : mulEquivtoLimit k K '' L'.val.fixingSubgroup = Set.preimage Subtype.val fix1 := by
        ext x
        constructor
        all_goals intro h
        · rcases h with ⟨α,hα1,hα2⟩
          simp only [Set.mem_preimage,←hα2]
          unfold_let fix1
          simp only [Set.mem_setOf_eq]
          unfold mulEquivtoLimit homtoLimit
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk]
          apply AlgEquiv.ext
          intro x
          apply Subtype.val_injective
          rw [← restrict_eq α x.1 L' x.2]
          simp only [AlgEquiv.one_apply]
          exact hα1 x
        · simp only [Set.mem_preimage] at h
          use (mulEquivtoLimit _ _).symm x
          constructor
          · unfold IntermediateField.fixingSubgroup
            apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr
            intro y hy
            simp only [AlgEquiv.smul_def]
            have fix := h.out
            set Aut := (mulEquivtoLimit _ _).symm x
            have : mulEquivtoLimit _ _ Aut = x := by
              unfold_let Aut
              simp only [MulEquiv.apply_symm_apply]
            rw [←this] at fix
            unfold mulEquivtoLimit homtoLimit at fix
            simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk] at fix
            have fix_y : AlgEquiv.restrictNormalHom L' Aut ⟨y, hy⟩ = ⟨y, hy⟩ := by
              simp only [fix, AlgEquiv.one_apply]
            rw [restrict_eq Aut y L' hy, fix_y]
          · simp only [MulEquiv.apply_symm_apply]
      have op : IsOpen fix1 := by
        rw [pre]
        have : IsOpen ({1} : Set ((finGalFunctor _ _).obj (op L'))) := by exact trivial
        exact C.isOpen_preimage {1} this
      rw [this]
      exact isOpen_induced op
    · simp only [Set.mem_preimage, map_one, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid]
      exact congrFun rfl

instance [IsGalois k K] : T2Space (K ≃ₐ[k] K) := krullTopology_t2

def limtoGalHomeo [IsGalois k K] :
    (ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K)) ≃ₜ (K ≃ₐ[k] K) :=
  Continuous.homeoOfEquivCompactToT2 limtoGalContinuous

noncomputable def continuousMulEquivtoLimit [IsGalois k K] :
    ContinuousMulEquiv (K ≃ₐ[k] K) (ProfiniteGrp.ofFiniteGrpLimit (finGalFunctor k K)) where
  __ := mulEquivtoLimit k K
  continuous_toFun := limtoGalHomeo.continuous_invFun
  continuous_invFun := limtoGalHomeo.continuous_toFun

end FiniteGaloisIntermediateField

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
