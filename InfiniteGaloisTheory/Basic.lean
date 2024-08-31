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

* `ContinuousMulEquiv`

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

variable (k K : Type*) [Field k] [Field K] [Algebra k K] -- [IsGalois k K]

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

instance : Category (FiniteGaloisIntermediateField k K) :=
  InducedCategory.category val

-- lemma val_injective : Function.Injective
--     fun (L : FiniteGaloisIntermediateField k K) ↦ L.val := by
--   rintro ⟨⟩ ⟨⟩ eq
--   dsimp at eq
--   simp [eq]

-- instance : PartialOrder (FiniteGaloisIntermediateField k K) :=
--   PartialOrder.lift val val_injective

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

lemma union_eq_univ'' (x y : K) [IsGalois k K] : ∃ L : (FiniteGaloisIntermediateField k K),
    x ∈ L.val ∧ y ∈ L.val := by
  let L' := normalClosure k (IntermediateField.adjoin k ({x,y} : Set K)) K
  letI : FiniteDimensional k (IntermediateField.adjoin k ({x,y} : Set K)) := by
    have hS : ∀ z ∈ ({x, y} : Set K), IsIntegral k z := fun z _ =>
      IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    exact IntermediateField.finiteDimensional_adjoin hS
  let L : (FiniteGaloisIntermediateField k K) := {
    L' with
    finiteDimensional := normalClosure.is_finiteDimensional k (IntermediateField.adjoin k ({x,y} : Set K)) K
    isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k ({x, y} : Set K)) K
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
    x ∈ L.val := by
  rcases (union_eq_univ'' (k := k) (K := K) x 1) with ⟨L, hL⟩
  exact ⟨L,hL.1⟩

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

lemma restrict_eq (σ : (K ≃ₐ[k] K)) (x : K) (Lx : FiniteGaloisIntermediateField k K)
  (hLx : x ∈ Lx.val) : σ x = ↑(((AlgEquiv.restrictNormalHom ↥Lx) σ) ⟨x, hLx⟩) := by
  change σ x = ((AlgEquiv.restrictNormal σ Lx) ⟨x,hLx⟩).1
  have := AlgEquiv.restrictNormal_commutes σ Lx ⟨x,hLx⟩
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
  rcases union_eq_univ' (k := k) x with ⟨Lx, hLx⟩
  have : (AlgEquiv.restrictNormalHom Lx σ₁ ⟨x, hLx⟩).val = (AlgEquiv.restrictNormalHom Lx σ₂ ⟨x, hLx⟩).val :=
    congr($this _ _)
  convert this
  all_goals apply restrict_eq

set_option synthInstance.maxHeartbeats 50000 in
lemma homtoLimit_lift' [IsGalois k K]
    (g : (ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K))).toProfinite.toTop)
    (x : K) {L : FiniteGaloisIntermediateField k K} (hL : x ∈ L.val)
    {L' : FiniteGaloisIntermediateField k K} (hL' : x ∈ L'.val) (h : L ⟶ L'):
    ((g.1 (op L)).1 ⟨x,hL⟩).1 = ((g.1 (op L')).1 ⟨x,hL'⟩).1
    := by
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
  (g : (ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K))).toProfinite.toTop)
  (x : K) {L : FiniteGaloisIntermediateField k K} (hL : x ∈ L.val) :
    (g.1 (op L)).1 ⟨x, hL⟩ =
    ((g.1 (op (Classical.choose (union_eq_univ' (k := k) x)))).1
      ⟨x, (Classical.choose_spec (union_eq_univ' (k := k) x))⟩).1
      := by
    let Lx := Classical.choose (union_eq_univ' (k := k) x)
    let hLx := Classical.choose_spec (union_eq_univ' (k := k) x)
    show ((g.1 (op L)).1 ⟨x,hL⟩).1 = ((g.1 (op Lx)).1 ⟨x,hLx⟩).1
    let Lm'' := (L.1 ⊔ Lx.1)
    letI : FiniteDimensional k Lm'' := IntermediateField.finiteDimensional_sup L.1 Lx.1
    let Lm' := normalClosure k Lm'' K
    let Lm : FiniteGaloisIntermediateField k K := mk Lm'
    have Lm''_le : Lm'' ≤ Lm.1 := IntermediateField.le_normalClosure Lm''
    have L_le : L.val ≤ Lm.val := le_trans (SemilatticeSup.le_sup_left L.1 Lx.1) Lm''_le
    have Lx_le : Lx.val ≤ Lm.val := le_trans (SemilatticeSup.le_sup_right L.1 Lx.1) Lm''_le
    have trans1 : ((g.1 (op L)).1 ⟨x, hL⟩).1 = ((g.1 (op Lm)).1 ⟨x, (L_le hL)⟩).1 :=
      homtoLimit_lift' g x hL (L_le hL) L_le.hom
    have trans2 : ((g.1 (op Lx)).1 ⟨x, hLx⟩).1 =
      ((g.1 (op Lm)).1 ⟨x,(L_le hL)⟩).1 := homtoLimit_lift' g x hLx (L_le hL) Lx_le.hom
    rw [trans1, trans2]

def bot : FiniteGaloisIntermediateField k K := ⟨⊥⟩

instance : Algebra k (bot (k := k) (K := K)) := bot.val.algebra'

theorem homtoLimit_surj [IsGalois k K] : Function.Surjective (homtoLimit (k := k) (K := K)) := by
  intro g
  let σ' : K →ₐ[k] K := {
    toFun := fun x => ((g.1 (op (Classical.choose (union_eq_univ' (k := k) x)))).1
        ⟨x,(Classical.choose_spec (union_eq_univ' (k := k) x))⟩).1
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
      rcases (union_eq_univ'' (k := k) x y) with ⟨L,hxL,hyL⟩
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
      rcases (union_eq_univ'' (k := k) x y) with ⟨L,hxL,hyL⟩
      have hxyL : x + y ∈ L.val := add_mem hxL hyL
      have hx := homtoLimit_lift g x hxL
      have hy := homtoLimit_lift g y hyL
      have hxy := homtoLimit_lift g (x + y) hxyL
      simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subsemiring.coe_carrier_toSubmonoid,
        Subalgebra.coe_toSubsemiring, IntermediateField.coe_toSubalgebra] at hx hy hxy
      rw [←hx,←hy, ←hxy]
      have : (⟨x + y, hxyL⟩ : L) = (⟨x, hxL⟩ : L) + (⟨y, hyL⟩ : L) := rfl
      rw [this, map_add]
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
      dsimp at this
      let z' := algebraMap k (bot (k := k) (K := K)) z
      have coe : algebraMap k K z = z' := rfl
      simp_rw [coe]
      have coe' : algebraMap k (bot (k := k) (K := K)) z = z' := rfl
      simp_rw [coe'] at this
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
  show σ'.toFun x.1  = ((g.1 L).1 x).1
  simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
    IntermediateField.coe_toSubalgebra, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  symm
  apply homtoLimit_lift

noncomputable def  MulEquivtoLimit [IsGalois k K] : (K ≃ₐ[k] K) ≃*
    ProfiniteGrp.limitOfFiniteGrp (finGalFunctor (k := k) (K := K)) :=
  MulEquiv.ofBijective homtoLimit ⟨homtoLimit_inj, homtoLimit_surj⟩

end FiniteGaloisIntermediateField

/-example : ProfiniteGrp := ProfiniteGroup.of (K ≃ₐ[k] K)-/
