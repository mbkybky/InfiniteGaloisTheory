import Mathlib.FieldTheory.Galois

open Algebra

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars _, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The `AlgEquiv` induced by an `AlgHom` from the domain of definition to the `fieldRange`. -/
noncomputable def AlgHom.fieldRange_toAlgEquiv {E : IntermediateField K L} (σ : E →ₐ[K] L) :
    E ≃ₐ[K] σ.fieldRange where
  toFun x := ⟨σ x, by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]⟩
  invFun y := Classical.choose (AlgHom.mem_fieldRange.mp y.2)
  left_inv x := have hs : Function.Injective σ := RingHom.injective σ
    have h : σ x ∈ σ.fieldRange := by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]
    hs (Classical.choose_spec (AlgHom.mem_fieldRange.mp h))
  right_inv y := Subtype.val_inj.mp (Classical.choose_spec (mem_fieldRange.mp y.2))
  map_mul' x y := Subtype.val_inj.mp (σ.toRingHom.map_mul x y)
  map_add' x y := Subtype.val_inj.mp (σ.toRingHom.map_add x y)
  commutes' x := Subtype.val_inj.mp (commutes σ x)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}

theorem AlgHom.fieldRange_toAlgEquiv_apply (σ : E →ₐ[K] L) (x : E) :
  (AlgHom.fieldRange_toAlgEquiv σ) x = σ x := rfl

theorem AlgEquiv.liftNormal_intermediateField_commutes [Normal K L] {E F : IntermediateField K L}
    (σ : E ≃ₐ[K] F) (x : E) : (AlgEquiv.liftNormal σ L) x = σ x := by
  have h : x.1 = algebraMap E L x := rfl
  rw [h, liftNormal_commutes]
  rfl

theorem normalClosure.eq_self_of_invariant_under_embedding {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Normal K L] (E : IntermediateField K L)
    (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : normalClosure K E L = E := by
  refine le_antisymm ?_ ((h (val E)).symm.trans_le (le_iSup AlgHom.fieldRange (val E)))
  intro x hx
  rw [normalClosure, mem_mk, Subalgebra.mem_toSubsemiring, mem_toSubalgebra] at hx
  exact iSup_le (fun σ ↦ (h σ).le) hx

/-- If `E` is an intermediateField of a normal extension `K/L`, and `E` remains invariant
under every `K`-algebra embedding `E →ₐ[K] L`, then `E/K` is normal. -/
theorem Normal.of_intermediateField_invariant_under_embedding [Normal K L]
    (E : IntermediateField K L) (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : Normal K E := by
  have hn := normalClosure.normal K E L
  rw [normalClosure.eq_self_of_invariant_under_embedding E h] at hn
  exact hn

/-- If `E` is an intermediateField of a normal extension `K/L`, and every element in `E`
remains in `E` after the action of every element in the Galois group, then `E/K` is normal. -/
theorem Normal.of_intermediateField_mem_invariant_under_embedding [Normal K L]
    (E : IntermediateField K L) (h : ∀ σ : L ≃ₐ[K] L, ∀ x : E, σ x.1 ∈ E) : Normal K E := by
  apply Normal.of_intermediateField_invariant_under_embedding E
  intro σ
  apply le_antisymm
  · intro y hy
    rcases AlgHom.mem_fieldRange.mp hy with ⟨x, hx⟩
    apply Set.mem_of_eq_of_mem _ (h (liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L) x)
    have h : x.1 = algebraMap E L x := rfl
    rw [← hx, h, liftNormal_commutes]
    rfl
  · intro y hy
    let τ := liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L
    let x : E := ⟨τ⁻¹ y, Set.mem_of_eq_of_mem rfl (h τ⁻¹ ⟨y, hy⟩)⟩
    rw [AlgHom.mem_fieldRange]
    use x
    have hx : σ x = algebraMap (σ.fieldRange) L ((AlgHom.fieldRange_toAlgEquiv σ) x) := rfl
    have hxt : (algebraMap E L) x = τ⁻¹ y := rfl
    have ht : τ (τ⁻¹ y) = (τ * τ⁻¹) y := rfl
    rw [hx, ← liftNormal_commutes, hxt, ht, mul_inv_cancel]
    rfl

/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `fixedField H` is Galois over `K`. -/
instance IsGalois.of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply Normal.of_intermediateField_mem_invariant_under_embedding (fixedField H)
    intro σ x τ
    calc _ = (σ * σ⁻¹ * τ.1 * σ) x.1 := by rw [mul_inv_cancel]; rfl
      _ = _ := by nth_rw 2 [← x.2 ⟨_ , (Subgroup.Normal.conj_mem hn τ.1 τ.2 σ⁻¹)⟩]; rfl

/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `Gal(fixedField H/K)` is isomorphic to
`Gal(L/K)⧸H`. -/
noncomputable def IsGalois.normal_aut_equiv_quotient [FiniteDimensional K L] [IsGalois K L]
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
  dsimp
  have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ x :=
    restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
  rw [← hs]
  exact Subtype.val_inj.mpr (h ⟨x, hx⟩)

end Galois
