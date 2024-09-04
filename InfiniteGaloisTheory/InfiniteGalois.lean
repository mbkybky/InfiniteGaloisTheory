/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao
-/

import InfiniteGaloisTheory.Basic

/-!

# The Fundamental Theorem of Infinite Galois Theory

In this file, we proved the fundamental theorem of infinite galois theory and the special case for
open subgroups and normal subgroups. We first verify that `IntermediateField.fixingSubgroup` and
`IntermediateField.fixedField` are inverse to each other between `IntermediateField` and closed subgroup of the
galois group.

# Main definitions and results

In `K/k`, for any intermediate field `L` :

* `fixingSubgroup_IsClosed` : the fixing subgroup of `L`
  (`Gal(K/L)`) is closed.

* `fixedField_fixingSubgroup` : the fixing field of the
  fixing subgroup of `L` is equal to `L` itself.

For any subgroup of `Gal(K/k)` `H` :

* `restrict_fixing_field` : For a Galois intermediate field `M`, the fixed field of the image of `H`
  restrict to `M` is equal to the fixed field of `H` intersecting `M`.

* `fixingSubgroup_fixedField` : If `H` is closed, the fixing subgroup of the fixed field of `H`
  is equal to `H` itself.

The fundamental theorem of infinite galois theory :

* `intermediateFieldEquivClosedSubgroup` : The order equivalent given by mapping any
  intermediate field `L` to the fixing subgroup of `L`, with its inverse mapping any
  closed subgroup of `Gal(K/k)` `H` to the fixed field of `H`. The composition is identity
  is given by above, and the compatibility with order follows easily.

Special cases :

* `OpeniffFinite` : The fixing subgroup of an intermediate field `L` is open iff
  `L` is finite dimensional.

* `NormaliffGalois` : The fixing subgroup of an intermediate field `L` is normal iff
  `L` is Galois.

-/

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section MissingLemmas

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (H : Subgroup (E ≃ₐ[F] E)) (K : IntermediateField F E)

namespace IntermediateField

@[simp]
theorem mem_fixedField_iff (x) :
    x ∈ fixedField H ↔ ∀ f ∈ H, f x = x := by
  show x ∈ MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]

end IntermediateField

end MissingLemmas

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

lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
    IntermediateField.fixedField L.fixingSubgroup = L := by
  letI : IsGalois L K := inferInstance
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have id : ∀ σ ∈ L.fixingSubgroup, σ x = x := hx
    let Lx := FiniteGaloisIntermediateField.adjoin L {x}
    have mem : x ∈ Lx.1 := FiniteGaloisIntermediateField.subset_adjoin _ _ (by simp)
    have : IntermediateField.fixedField (⊤ : Subgroup (Lx ≃ₐ[L] Lx)) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ ∈ (⊥ : IntermediateField L Lx) := by
      rw [← this, IntermediateField.mem_fixedField_iff]
      intro f _
      rcases AlgEquiv.restrictNormalHom_surjective (K₁ := Lx) K f with ⟨σ,hσ⟩
      apply Subtype.val_injective
      rw [←hσ, ←InfiniteGalois.restrict_eq σ x Lx mem]
      dsimp
      have := id <| (IntermediateField.fixingSubgroupEquiv L).symm σ
      simp only [SetLike.coe_mem, true_implies] at this
      convert this
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr fun ⦃x⦄ a ↦ a

lemma fixedField_bot [IsGalois k K] :
    IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by
  rw [← IntermediateField.fixingSubgroup_bot, fixedField_fixingSubgroup]

lemma restrict_fixing_field (H : Subgroup (K ≃ₐ[k] K)) [IsGalois k K] (L : IntermediateField k K)
    [IsGalois k L] :
    (IntermediateField.fixedField H) ⊓ L = IntermediateField.lift (IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) H)) := by
  apply SetLike.ext'
  ext x
  simp only [SetLike.mem_coe]
  constructor
  all_goals intro h
  · have xL := h.out.2
    have : (⟨x,xL⟩ : L).1 = x := rfl
    rw [←this]
    apply (IntermediateField.mem_lift (⟨x,xL⟩ : L)).mpr
    rw [IntermediateField.mem_fixedField_iff]
    simp only [Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro σ hσ
    show ((AlgEquiv.restrictNormal σ L) ⟨x, xL⟩) = ⟨x, xL⟩
    apply Subtype.val_injective
    dsimp
    have := (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm
    nth_rw 2 [←(h.out.1 ⟨σ,hσ⟩)]
    convert this
    exact id (Eq.symm this)
  · have xL := IntermediateField.lift_le _ h
    have : (⟨x,xL⟩ : L).1 = x := rfl
    rw [←this] at h
    apply (IntermediateField.mem_lift (⟨x,xL⟩ : L)).mp at h
    simp only [IntermediateField.mem_inf, xL, and_true]
    rw [IntermediateField.mem_fixedField_iff] at h ⊢
    simp only [Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
    intro σ hσ
    have : ((AlgEquiv.restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by
      rw [h σ hσ]
    nth_rw 2 [←this]
    show σ x = ((AlgEquiv.restrictNormal σ L) ⟨x, xL⟩).1
    have := AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
    convert this
    exact id (Eq.symm this)

lemma fixingSubgroup_fixedField (H : ClosedSubgroup (K ≃ₐ[k] K)) [IsGalois k K] :
    (IntermediateField.fixedField H).fixingSubgroup = H.1 := by
  apply le_antisymm
  · intro σ hσ
    by_contra h
    have op : IsOpen H.carrierᶜ := by
      have := H.isClosed'
      exact IsClosed.isOpen_compl
    have nhd : H.carrierᶜ ∈ nhds σ := IsOpen.mem_nhds op h
    rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhd
    rcases nhd with ⟨b,⟨gp,⟨L,hL,eq'⟩,eq⟩,sub⟩
    dsimp at eq
    rw [←eq'] at eq
    have sub : σ • b ⊆ H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    let L' : FiniteGaloisIntermediateField k K := {
      normalClosure k L K with
      to_finiteDimensional := by
        have := hL.out
        exact normalClosure.is_finiteDimensional k L K
      to_isGalois := IsGalois.normalClosure k L K
    }
    letI := L'.to_finiteDimensional
    have compl : σ • L'.1.fixingSubgroup.carrier ⊆ H.carrierᶜ :=
      fun ⦃a⦄ d ↦ sub ((Set.set_smul_subset_set_smul_iff.mpr <| eq ▸ (fun σ h =>
      (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr fun y hy => (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp
      h y (IntermediateField.le_normalClosure L hy))) d)
    have fix : ∀ x ∈ IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x := by
      intro x hx
      simp only [IntermediateField.mem_inf] at hx
      apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp at hσ
      exact hσ x hx.1
    rw [restrict_fixing_field H.1 L'.1] at fix
    have : (AlgEquiv.restrictNormalHom L') σ ∈ (Subgroup.map (AlgEquiv.restrictNormalHom L') H.1) := by
      rw [←IntermediateField.fixingSubgroup_fixedField
        (Subgroup.map (AlgEquiv.restrictNormalHom L') H.1)]
      set cH := (Subgroup.map (AlgEquiv.restrictNormalHom L') H.toSubgroup)
      apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
      intro y hy
      have : y.1 ∈ IntermediateField.lift (IntermediateField.fixedField cH) :=
        (IntermediateField.mem_lift y).mpr hy
      have coe : y = ⟨y.1,y.2⟩ := rfl
      rw [AlgEquiv.smul_def, coe]
      apply Subtype.val_injective
      rw [←restrict_eq σ y.1 L' y.2, fix y.1 this]
    rcases this with ⟨h,hh,sub⟩
    have : h ∈ σ • L'.1.fixingSubgroup.carrier := by
      use σ⁻¹ * h
      simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
        smul_eq_mul, mul_inv_cancel_left, and_true]
      apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr
      show ∀ y ∈ L'.1, (σ⁻¹ * h) • y = y
      intro y hy
      simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
      have : h y = σ y := by
        have : ((AlgEquiv.restrictNormalHom L') h ⟨y,hy⟩).1 =
          ((AlgEquiv.restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [sub]
        rw [←restrict_eq h y L' hy, ←restrict_eq σ y L' hy] at this
        exact this
      rw [this]
      have : σ⁻¹ (σ y) = (σ⁻¹ * σ) y := rfl
      simp only [this, inv_mul_cancel, AlgEquiv.one_apply]
    absurd compl
    apply Set.not_subset.mpr
    use h
    simp only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid, not_not, true_and]
    exact hh
  · exact (IntermediateField.le_iff_le H.toSubgroup (IntermediateField.fixedField H.toSubgroup)).mp
      fun ⦃x⦄ a ↦ a

def intermediateFieldEquivClosedSubgroup [IsGalois k K] :
  IntermediateField k K ≃o (ClosedSubgroup (K ≃ₐ[k] K))ᵒᵈ where
    toFun := fun L =>
      { L.fixingSubgroup with
        isClosed' := fixingSubgroup_IsClosed L }
    invFun := fun H => IntermediateField.fixedField H.1
    left_inv := by
      simp only [Function.LeftInverse]
      intro L
      exact fixedField_fixingSubgroup L
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse]
      intro H
      simp_rw [fixingSubgroup_fixedField H]
      rfl
    map_rel_iff' := by
      intro L₁ L₂
      simp only [Equiv.coe_fn_mk]
      show L₁.fixingSubgroup ≥ L₂.fixingSubgroup ↔ L₁ ≤ L₂
      rw [← fixedField_fixingSubgroup L₂, IntermediateField.le_iff_le, fixedField_fixingSubgroup L₂]

theorem OpeniffFinite (L : IntermediateField k K) [IsGalois k K] :
  IsOpen (intermediateFieldEquivClosedSubgroup.toFun L).carrier ↔
  (FiniteDimensional k L) := by
  constructor
  all_goals intro h
  · have : (intermediateFieldEquivClosedSubgroup.toFun L).carrier ∈ nhds 1 :=
      IsOpen.mem_nhds h (congrFun rfl)
    rw [GroupFilterBasis.nhds_one_eq] at this
    rcases this with ⟨S,⟨gp,⟨M,hM,eq'⟩,eq⟩,sub⟩
    simp only [← eq'] at eq
    rw [←eq] at sub
    have := hM.out
    let L' : FiniteGaloisIntermediateField k K := {
      normalClosure k M K with
      to_finiteDimensional := normalClosure.is_finiteDimensional k M K
      to_isGalois := IsGalois.normalClosure k M K
    }
    have : L'.1.fixingSubgroup.carrier ⊆ (intermediateFieldEquivClosedSubgroup.1.1 L).carrier := by
      have : M ≤ L'.1 := IntermediateField.le_normalClosure M
      rw [← fixedField_fixingSubgroup L'.1, IntermediateField.le_iff_le] at this
      exact fun ⦃a⦄ a_1 ↦ sub (this a_1)
    simp [intermediateFieldEquivClosedSubgroup] at this
    have : L'.1.fixingSubgroup ≤ L.fixingSubgroup := this
    have le : L ≤ L'.1 := by
      rw [← fixedField_fixingSubgroup L'.1, IntermediateField.le_iff_le]
      exact this
    letI := L'.to_finiteDimensional
    exact FiniteDimensional_of_le le
  · simp only [intermediateFieldEquivClosedSubgroup, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
    apply IntermediateField.fixingSubgroup_isOpen

theorem NormaliffGalois (L : IntermediateField k K) [IsGalois k K] :
  Subgroup.Normal (intermediateFieldEquivClosedSubgroup.toFun L).1 ↔
  IsGalois k L := by
  constructor
  all_goals intro h
  · let f : L → IntermediateField k K :=
      fun x => IntermediateField.lift <| IntermediateField.fixedField <| Subgroup.map
        (AlgEquiv.restrictNormalHom (FiniteGaloisIntermediateField.adjoin k {x.1}))
        L.fixingSubgroup
    have h' (x : K) : (Subgroup.map (AlgEquiv.restrictNormalHom
      (FiniteGaloisIntermediateField.adjoin k {x})) L.fixingSubgroup).Normal := by
      set f := AlgEquiv.restrictNormalHom (F := k) (K₁ := K)
        (FiniteGaloisIntermediateField.adjoin k {x})
      have : Function.Surjective f := AlgEquiv.restrictNormalHom_surjective K
      simp only [intermediateFieldEquivClosedSubgroup, Equiv.toFun_as_coe, Equiv.coe_fn_mk] at h
      exact Subgroup.Normal.map h f this
    have n' (l : L) : IsGalois k (IntermediateField.fixedField <| Subgroup.map
        (AlgEquiv.restrictNormalHom (FiniteGaloisIntermediateField.adjoin k {l.1}))
        L.fixingSubgroup) := by
        letI := IsGalois.of_fixedField_normal_subgroup (Subgroup.map (AlgEquiv.restrictNormalHom
          (FiniteGaloisIntermediateField.adjoin k {l.1})) L.fixingSubgroup)
        set cH := (Subgroup.map (AlgEquiv.restrictNormalHom
          (FiniteGaloisIntermediateField.adjoin k {l.1})) L.fixingSubgroup)
        let e : ↥(IntermediateField.fixedField cH) ≃ₐ[k]
          IntermediateField.lift (IntermediateField.fixedField cH) := {
            toFun := fun x => ⟨x.1.1,(IntermediateField.mem_lift x.1).mpr x.2⟩
            invFun := fun x => by
              have := x.2
              unfold_let cH at this
              simp_rw [←restrict_fixing_field] at this
              have mem : x.1 ∈ (FiniteGaloisIntermediateField.adjoin k {↑l}).1 := by
                have le : IntermediateField.fixedField L.fixingSubgroup ⊓
                  (FiniteGaloisIntermediateField.adjoin k {l.1}).1 ≤
                  (FiniteGaloisIntermediateField.adjoin k {l.1}).1 := inf_le_right
                exact le this
              use ⟨x.1,mem⟩
              have : (⟨x.1, mem⟩ : { x // x ∈ (FiniteGaloisIntermediateField.adjoin k {l.1}).1 }).1
                ∈ IntermediateField.lift (IntermediateField.fixedField cH) := x.2
              exact (IntermediateField.mem_lift ⟨x.1, mem⟩).mp this
            left_inv := by simp only [Function.LeftInverse, Subtype.coe_eta, id_eq, implies_true]
            right_inv := by simp only [Function.RightInverse, Function.LeftInverse, id_eq,
              Subtype.coe_eta, implies_true]
            map_mul' := fun _ _ => rfl
            map_add' := fun _ _ => rfl
            commutes' := fun _ => rfl
          }
        exact IsGalois.of_algEquiv e
    have n : Normal k ↥(⨆ (l : L), f l):= IntermediateField.normal_iSup k K f
    have : (⨆ (l : L), f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        unfold_let f
        dsimp
        simp only [intermediateFieldEquivClosedSubgroup, Equiv.toFun_as_coe, Equiv.coe_fn_mk] at h
        rw [←restrict_fixing_field L.fixingSubgroup (FiniteGaloisIntermediateField.adjoin k {l.1}),
          fixedField_fixingSubgroup L]
        exact inf_le_left
      · intro l hl
        apply le_iSup f ⟨l,hl⟩
        unfold_let f
        dsimp
        rw [←restrict_fixing_field L.fixingSubgroup (FiniteGaloisIntermediateField.adjoin k {l}),
          fixedField_fixingSubgroup L]
        simp only [IntermediateField.mem_inf, hl, true_and]
        apply IntermediateField.le_normalClosure
        exact IntermediateField.mem_adjoin_simple_self k l
    rw [this] at n
    letI : Algebra.IsSeparable k L := Algebra.isSeparable_tower_bot_of_isSeparable k L K
    apply IsGalois.mk
  · have : (intermediateFieldEquivClosedSubgroup.toFun L).1 =
      (AlgEquiv.restrictNormalHom L).ker := by
      ext σ
      show σ ∈ L.fixingSubgroup ↔ (AlgEquiv.restrictNormalHom L) σ = 1
      have iff1 : σ ∈ fixingSubgroup (K ≃ₐ[k] K) (L : Set K) ↔ ∀ y ∈ (L : Set K), σ • y = y := by
        apply mem_fixingSubgroup_iff
      apply Iff.trans iff1
      simp only [SetLike.mem_coe, AlgEquiv.smul_def]
      show (∀ y ∈ L, σ y = y) ↔ (σ.restrictNormal L) = 1
      constructor
      all_goals intro hyp
      · ext x
        simp only [AlgEquiv.one_apply, SetLike.coe_eq_coe]
        apply Subtype.val_injective
        rw [←hyp x.1 x.2]
        exact AlgEquiv.restrictNormal_commutes σ L x
      · intro y hy
        have : σ y = σ.restrictNormal L ⟨y,hy⟩ :=
          (AlgEquiv.restrictNormal_commutes σ L ⟨y,hy⟩).symm
        rw [this,hyp, AlgEquiv.one_apply]
    rw [this]
    exact MonoidHom.normal_ker (AlgEquiv.restrictNormalHom L)

end InfiniteGalois
