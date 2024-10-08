/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jingting Wang
-/
import Mathlib.FieldTheory.Galois

open Algebra

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)

/-- The `AlgEquiv` induced by an `AlgHom` from the domain of definition to the `fieldRange`. -/
noncomputable def AlgHom.toAlgEquiv_fieldRange {E : Type*} [Field E] [Algebra K E] (σ : L →ₐ[K] E) :
    L ≃ₐ[K] σ.fieldRange where
  toFun x := ⟨σ x, by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]⟩
  invFun y := Classical.choose (AlgHom.mem_fieldRange.mp y.2)
  left_inv x := have hs : Function.Injective σ := RingHom.injective σ
    have h : σ x ∈ σ.fieldRange := by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]
    hs (Classical.choose_spec (AlgHom.mem_fieldRange.mp h))
  right_inv y := Subtype.val_inj.mp (Classical.choose_spec (mem_fieldRange.mp y.2))
  map_mul' x y := Subtype.val_inj.mp (σ.toRingHom.map_mul x y)
  map_add' x y := Subtype.val_inj.mp (σ.toRingHom.map_add x y)
  commutes' x := Subtype.val_inj.mp (commutes σ x)

theorem AlgHom.toAlgEquiv_fieldRange_apply (σ : E →ₐ[K] L) (x : E) :
  (AlgHom.toAlgEquiv_fieldRange σ) x = σ x := rfl

theorem AlgEquiv.liftNormal_intermediateField_commutes [Normal K L] {E F : IntermediateField K L}
    (σ : E ≃ₐ[K] F) (x : E) : (AlgEquiv.liftNormal σ L) x = σ x := by
  have h : x.1 = algebraMap E L x := rfl
  rw [h, liftNormal_commutes]
  rfl

namespace Normal

/-- If `E` is an intermediate field of a normal extension `K / L`, and every element in `E`
remains in `E` after the action of every element in the Galois group, then `E / K` is normal. -/
private lemma of_intermediateField_mem_invariant_under_embedding [Normal K L]
    (E : IntermediateField K L) (h₀ : ∀ σ : L ≃ₐ[K] L, ∀ x : E, σ x.1 ∈ E) : Normal K E := by
  apply normal_iff_forall_map_le'.mpr
  intro σ h hy
  have : h ∈ (IntermediateField.map σ.toAlgHom E : Set L) := hy
  rcases this with ⟨x,hx⟩
  rw [← hx.2]
  convert h₀ σ ⟨x,hx.1⟩

end Normal

/-- If `H` is a subgroup of `Gal(L / K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut [FiniteDimensional K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars _, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

section

open scoped Pointwise

private theorem Subgroup.Normal.of_conjugate_fixed {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ g : G, (MulAut.conj g) • H = H) : H.Normal := by
  constructor
  intro n hn g
  rw [← h g, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
    ← mul_assoc, inv_mul_cancel, one_mul]
  exact hn

end

namespace IsGalois

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `fixedField H` is Galois over `K`. -/
instance of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply Normal.of_intermediateField_mem_invariant_under_embedding (fixedField H)
    intro σ x τ
    calc _ = (σ * σ⁻¹ * τ.1 * σ) x.1 := by rw [mul_inv_cancel]; rfl
      _ = _ := by nth_rw 2 [← x.2 ⟨_ , (Subgroup.Normal.conj_mem hn τ.1 τ.2 σ⁻¹)⟩]; rfl

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `Gal(fixedField H / K)` is isomorphic to
`Gal(L / K) ⧸ H`. -/
noncomputable def normalAutEquivQuotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    ((fixedField H) ≃ₐ[K] (fixedField H)) ≃* (L ≃ₐ[K] L) ⧸ H := by
  apply MulEquiv.symm <| (quotientMulEquivOfEq ((fixingSubgroup_fixedField H).symm.trans _)).trans
    <| quotientKerEquivOfSurjective (restrictNormalHom (fixedField H)) <|
      restrictNormalHom_surjective L
  ext σ
  apply (((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).trans ⟨fun h ⟨x, hx⟩ ↦ Subtype.val_inj.mp <|
    (restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩).trans (h x hx) , _⟩).trans
      AlgEquiv.ext_iff.symm).trans (MonoidHom.mem_ker (restrictNormalHom (fixedField H))).symm
  intro h x hx
  have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ • x :=
    restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
  rw [← hs]
  exact Subtype.val_inj.mpr (h ⟨x, hx⟩)

open scoped Pointwise

theorem fixingSubgroup_conjugate_of_map (σ : L ≃ₐ[K] L) :
    E.fixingSubgroup = (MulAut.conj σ⁻¹) • ((IntermediateField.map σ E).fixingSubgroup) := by
  ext τ
  have h1 : τ ∈ (MulAut.conj σ⁻¹ • (IntermediateField.map σ E).fixingSubgroup :
    Subgroup (L ≃ₐ[K] L)) ↔ ∀ x : ((IntermediateField.map σ E) : IntermediateField K L),
    σ (τ (σ⁻¹ x)) = x := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, MulAut.smul_def,
      MulAut.conj_apply]
    exact Iff.rfl
  have h2 : τ ∈ E.fixingSubgroup ↔ ∀ x : E, τ x = x := Iff.rfl
  have h3 : ∀ x : L, (x ∈ ((IntermediateField.map σ E) : IntermediateField K L) ↔
      ∃ y : E, x = σ y) :=
    fun x ↦ ⟨fun ⟨y, hy, heq⟩ ↦ ⟨⟨y, hy⟩, heq.symm⟩, fun ⟨⟨y, hy⟩, heq⟩ ↦ ⟨y, hy, heq.symm⟩⟩
  rw [h1, h2]
  exact ⟨
    fun h ↦ (fun x ↦ (by
      obtain ⟨y, hy⟩ := (h3 x).mp x.2
      rw [hy, show σ⁻¹ (σ y) = y from σ.left_inv y, h y])),
    fun h ↦ (fun x ↦ (by
      have : σ (τ (σ⁻¹ (σ x))) = σ x := h ⟨σ x, (h3 (σ x)).mpr ⟨x, rfl⟩⟩
      rw [show σ⁻¹ (σ x) = x from σ.left_inv x, EmbeddingLike.apply_eq_iff_eq] at this
      exact this))⟩

/-- Let `E` be an intermediateField of a Galois extension `L / K`. If `E / K` is
Galois extension, then `E.fixingSubgroup` is a normal subgroup of `Gal(L / K)`. -/
instance fixingSubgroup_normal_of_isGalois [IsGalois K L] [IsGalois K E] :
    E.fixingSubgroup.Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro σ
  have : E = ((IntermediateField.map (σ⁻¹ : L ≃ₐ[K] L) E) : IntermediateField K L) :=
    (IntermediateField.normal_iff_forall_map_eq'.mp inferInstance σ⁻¹).symm
  nth_rw 1 [this, IsGalois.fixingSubgroup_conjugate_of_map E σ⁻¹, inv_inv]

end IsGalois

namespace IntermediateField


--after lift
/--The algEquiv between an intermediate field and its lift-/
def lift_algEquiv (F : IntermediateField K E) :
    ↥F ≃ₐ[K] (IntermediateField.lift F) where
  toFun := fun x => ⟨x.1.1,(mem_lift x.1).mpr x.2⟩
  invFun := fun x => ⟨⟨x.1, IntermediateField.lift_le F x.2⟩,
    (mem_lift ⟨x.1, IntermediateField.lift_le F x.2⟩).mp x.2⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

--mark as private
lemma finiteDimensional_of_le {M N : IntermediateField K L} (le : M ≤ N) [FiniteDimensional K N] :
    FiniteDimensional K M := by
  let i : M →ₐ[K] N := {
    toFun := fun x => ⟨x.1, le x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl
  }
  have inj : Function.Injective i := fun x y h => by
    apply_fun Subtype.val at h
    exact Subtype.val_injective h
  exact FiniteDimensional.of_injective (AlgHom.toLinearMap i) inj

end IntermediateField

end Galois
