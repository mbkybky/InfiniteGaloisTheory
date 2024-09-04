/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu
-/
import InfiniteGaloisTheory.ProFinite.Basic
import InfiniteGaloisTheory.ProFinite.Limit
/-!

# A profinite Group is the projective limit of finite groups

-/

suppress_compilation

universe u v

open CategoryTheory Topology

section limitofProfinite

namespace ProfiniteGrp

section

abbrev OpenNormalSubgroup (G : ProfiniteGrp) := {H : Subgroup G // H.Normal ∧ IsOpen (H : Set G)}

def diagramOfProfiniteGrp (P : ProfiniteGrp) :
  OpenNormalSubgroup P ⥤ FiniteGrp := {
    obj := fun ⟨H, _, hH⟩ =>
      letI : Finite (P ⧸ H) := finite_quotient_of_open_subgroup H hH
      FiniteGrp.of (P ⧸ H)
    map := fun {H K} fHK =>
      let ⟨H, _, _⟩ := H
      let ⟨K, _, _⟩ := K
      QuotientGroup.map H K (.id _) $ Subgroup.comap_id K ▸ leOfHom fHK
    map_id := fun ⟨x, _, _⟩ => by
      simp only [QuotientGroup.map_id, id_apply]; rfl
    map_comp := fun {X Y Z} f g =>
      let ⟨x, _, _⟩ := X
      let ⟨y, _, _⟩ := Y
      let ⟨z, _, _⟩ := Z
      (QuotientGroup.map_comp_map x y z (.id _) (.id _) (Subgroup.comap_id y ▸ leOfHom f)
        (Subgroup.comap_id z ▸ leOfHom g)).symm
  }

def canonicalMap (P : ProfiniteGrp.{u}) : P ⟶ ofFiniteGrpLimit (diagramOfProfiniteGrp P) where
  toFun := fun p => {
    val := fun ⟨H, _, _⟩ => QuotientGroup.mk p
    property := fun ⟨A, _, _⟩ ⟨B, _, _⟩ _ => rfl
  }
  map_one' := Subtype.val_inj.mp (by ext ⟨H, _, _⟩; rfl)
  map_mul' := fun x y => Subtype.val_inj.mp (by ext ⟨H, _, _⟩; rfl)
  continuous_toFun := by
    dsimp
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro ⟨H, hH, hHO⟩
    dsimp
    apply Continuous.mk
    intro s _
    rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
    apply isOpen_iUnion; intro i
    apply isOpen_iUnion; intro ih
    rw [QuotientGroup.preimage_mk_eq_coset]
    exact IsOpen.leftCoset hHO (Quotient.out' i)

theorem denseCanonicalMap (P : ProfiniteGrp.{u}) : Dense $ Set.range (canonicalMap P) :=
  dense_iff_inter_open.mpr
    fun U hUO hUNonempty => (by
      let uDefault := hUNonempty.some
      let uDefaultSpec : uDefault ∈ U := hUNonempty.some_mem
      rcases hUO with ⟨s, hsO, hsv⟩
      let uMemPiOpen := isOpen_pi_iff.mp hsO
      simp_rw [← hsv] at uDefaultSpec
      rw [Set.mem_preimage] at uDefaultSpec
      specialize uMemPiOpen _ uDefaultSpec
      rcases uMemPiOpen with ⟨J, fJ, h_ok_and_in_s⟩
      let subg: J → Subgroup P := fun ⟨j, _⟩ => j.val
      haveI subgNormal: ∀ j : J, (subg j).Normal := fun ⟨j, _⟩ => j.prop.1
      let M := iInf subg
      haveI hM : M.Normal := Subgroup.normal_iInf_normal subgNormal
      haveI hMOpen : IsOpen (M : Set P) := by
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite fun ⟨i, _⟩ => i.prop.2
      let m : P.OpenNormalSubgroup := ⟨M, hM, hMOpen⟩
      rcases uDefault with ⟨spc, hspc⟩
      have : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
      rcases this (spc m) with ⟨origin, horigin⟩
      let map_origin := (canonicalMap P).toFun origin
      use map_origin
      constructor
      · have : map_origin.val ∈ J.toSet.pi fJ := fun a a_in_J => by
          let M_to_Na : m ⟶ a := (iInf_le subg ⟨a, a_in_J⟩).hom
          rw [← (P.canonicalMap.toFun origin).property M_to_Na]
          show (P.diagramOfProfiniteGrp.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
          rw [horigin, hspc M_to_Na]
          exact (h_ok_and_in_s.1 a a_in_J).2
        exact hsv ▸ h_ok_and_in_s.2 this
      exact ⟨origin, rfl⟩
    )

theorem surjectiveCanonicalMap (P : ProfiniteGrp.{u}) : Function.Surjective (canonicalMap P) := by
  have : IsClosedMap P.canonicalMap := P.canonicalMap.continuous_toFun.isClosedMap
  haveI compact_s: IsCompact (Set.univ : Set P) := CompactSpace.isCompact_univ
  have : IsClosed (P.canonicalMap '' Set.univ) := this _ $ IsCompact.isClosed compact_s
  have dense_map := Dense.closure_eq $ denseCanonicalMap P
  apply closure_eq_iff_isClosed.mpr at this
  rw [Set.image_univ] at this
  rw [dense_map] at this
  exact Set.range_iff_surjective.mp (id this.symm)

end

section ProfiniteGrp

open scoped Pointwise

theorem exist_open_symm_subnhds {G : ProfiniteGrp} {W : Set G}
(WClopen : IsClopen W) (einW : 1 ∈ W) :∃ V : Set G, IsOpen V ∧ V = V⁻¹ ∧ 1 ∈ V ∧ V ⊆ W ∧ W * V ⊆ W
:= by
  let μ : G × G → G := fun (x, y) ↦ x * y
  have μCont : Continuous μ := continuous_mul

  let μinvW := μ⁻¹' W ∩ (W ×ˢ W)
  have μinvWsubWp : μinvW ⊆ (W ×ˢ W) := Set.inter_subset_right

  have mem_μinvW : ∀ w : W, ((w : G), 1) ∈ μinvW := by
    intro w
    unfold_let μinvW
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    constructor ; simp only [mul_one, Subtype.coe_prop, μ]
    constructor ; simp only [Subtype.coe_prop]
    exact einW

  have μinvWOpen : IsOpen μinvW := by
    unfold_let μinvW
    apply IsOpen.inter
    apply μCont.isOpen_preimage W <| IsClopen.isOpen WClopen
    apply IsOpen.prod <;> (apply IsClopen.isOpen WClopen)

  have mem_μinvWOpen : ∀ w : W, ∃ (Uw : Set G) (Vw : Set G), IsOpen Uw ∧ IsOpen Vw ∧ (w : G)  ∈ Uw ∧
    1 ∈ Vw ∧ Uw ×ˢ Vw ⊆ μinvW := by
    intro w
    apply isOpen_prod_iff.mp μinvWOpen w 1 (mem_μinvW w)

  clear μCont mem_μinvW μinvWOpen

  let Uw := fun w ↦ Classical.choose (mem_μinvWOpen w)
  let spec1 := fun w ↦ Classical.choose_spec (mem_μinvWOpen w)
  let Vw' := fun w ↦ Classical.choose (spec1 w)
  let spec2 := fun w ↦ Classical.choose_spec (spec1 w)
  let Vw := fun w ↦ (Vw' w) ∩ (Vw' w)⁻¹

  have spec3 : ∀ w : W, (Uw w) ⊆ W ∧ (Vw' w) ⊆ W :=by
    intro w
    rcases spec2 w with ⟨_,_,_,_,s5⟩
    have : (Uw w) ×ˢ (Vw' w) ⊆ W ×ˢ W :=by
      intro g gin
      exact μinvWsubWp (s5 gin)
    rw[Set.prod_subset_prod_iff] at this
    rcases this with _|empty|empty
    assumption
    repeat
    rw[Set.eq_empty_iff_forall_not_mem] at empty
    tauto

  have spec4 : ∀ w : W, IsOpen (Vw w) ∧ 1 ∈ (Vw w) ∧  (Vw w) = (Vw w)⁻¹ ∧ (Vw w) ⊆ W := by
    intro w
    rcases spec2 w with ⟨_,s2,_,s4,_⟩
    rcases spec3 w with ⟨_,s7⟩
    constructor
    · apply IsOpen.inter s2 (IsOpen.inv s2)
    constructor
    · apply Set.mem_inter s4
      simp only [Set.mem_inv, inv_one]
      exact s4
    constructor
    · ext x
      unfold_let Vw
      simp only [Set.mem_inter_iff, Set.mem_inv, Set.inter_inv, inv_inv]
      exact And.comm
    intro x ⟨xV,_⟩
    exact s7 xV

  have UOpen :=  fun w ↦ (spec2 w).1
  have VOpen := fun w ↦ (spec4 w).1
  have einV := fun w ↦ (spec4 w).2.1
  have VSymm := fun w ↦ (spec4 w).2.2.1
  have VsubW := fun w ↦ (spec4 w).2.2.2
  have cover : W ⊆ ⋃ w : W, Uw w := by
    intro x xinW
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    use x, xinW
    exact (spec2 ⟨x,xinW⟩).2.2.1
  clear spec3 spec4 μinvWsubWp

  rcases IsCompact.elim_finite_subcover (IsClosed.isCompact (IsClopen.isClosed WClopen)) _ UOpen cover
  with ⟨fin,fincover⟩
  have : Nonempty fin :=by
    by_contra empty
    rw [nonempty_subtype] at empty
    push_neg at empty
    apply Finset.eq_empty_of_forall_not_mem at empty
    simp_rw [empty, Finset.not_mem_empty, exists_and_left, Set.iUnion_of_empty, Set.iUnion_empty,
      Set.subset_empty_iff,Set.eq_empty_iff_forall_not_mem] at fincover
    tauto
  let w0 := Classical.choice this

  use ⋂ w ∈ fin , Vw w
  constructor
  · exact isOpen_biInter_finset fun w _ ↦ VOpen w
  constructor
  · ext x
    constructor <;>
    · intro h
      simp at h ⊢
      intro w winW winfin
      specialize h w winW winfin
      rw[VSymm ⟨w,winW⟩]
      simp only [Set.mem_inv, inv_inv, h]
  constructor
  · simp_rw [Set.mem_iInter]
    intro w _
    exact einV w
  constructor
  · intro x xinInter
    simp_rw [Set.mem_iInter] at xinInter
    specialize xinInter w0 w0.prop
    exact (VsubW w0) xinInter
  intro a ainmul
  rw[Set.mem_mul] at ainmul
  rcases ainmul with ⟨x,xinW,y,yinInter,xmuly⟩
  have := fincover xinW
  simp_rw [ Set.mem_iUnion, exists_prop', nonempty_prop] at this
  rcases this with ⟨w,winfin,xinU⟩
  simp_rw [Set.mem_iInter] at yinInter
  have yinV := Set.mem_of_mem_inter_left (yinInter w winfin)
  have := Set.mem_of_mem_inter_left <| (spec2 w).2.2.2.2 <| Set.mk_mem_prod xinU yinV
  simpa only [Set.mem_preimage, xmuly, μ] using this

def open_subgroup_subnhds {G : ProfiniteGrp} {W : Set G}
(WClopen : IsClopen W) (einW : 1 ∈ W) : Subgroup G where
  carrier := {x : G | ∃ n : ℕ, x ∈ Classical.choose (exist_open_symm_subnhds WClopen einW) ^ n}
  mul_mem':= by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rcases ha with ⟨na, hna⟩
    rcases hb with ⟨nb, hnb⟩
    use na + nb
    rw [pow_add]
    exact Set.mul_mem_mul hna hnb
  one_mem':= by
    simp only [Set.mem_setOf_eq]
    use 1
    rw [pow_one]
    exact (Classical.choose_spec (exist_open_symm_subnhds WClopen einW)).2.2.1
  inv_mem':= by
    simp only [Set.mem_setOf_eq, forall_exists_index] at *
    intro x m hm
    use m
    have : ∀ n : ℕ, ∀ x : G, x ∈ Classical.choose (exist_open_symm_subnhds WClopen einW) ^ n → x⁻¹ ∈ Classical.choose (exist_open_symm_subnhds WClopen einW) ^ n := by
      intro n
      induction' n with k hk
      · rw [pow_zero]
        intro x hx
        rw [hx]
        exact Set.mem_one.mpr inv_one
      · intro x hx
        rw [add_comm]
        rw [pow_add, pow_one] at *
        rcases hx with ⟨a, ha, b, hb, hyp⟩
        simp only at hyp
        rw [← hyp, DivisionMonoid.mul_inv_rev a b]
        apply Set.mul_mem_mul
        · rw [(Classical.choose_spec (exist_open_symm_subnhds WClopen einW)).2.1]
          exact Set.inv_mem_inv.mpr hb
        · exact hk a ha
    exact this m x hm

theorem open_subgroup_subnhds_spec {G : ProfiniteGrp} {W : Set G}
(WClopen : IsClopen W) (einW : 1 ∈ W) :
IsOpen ((open_subgroup_subnhds WClopen einW) : Set G) ∧
((open_subgroup_subnhds WClopen einW) : Set G) ⊆ W :=sorry

def OpenNormalSubgroup_subnhds {G : ProfiniteGrp} {U : Set G}
(UOpen : IsClopen U) (einU : 1 ∈ U) : OpenNormalSubgroup G :=sorry

theorem OpenNormalSubgroup_subnhds_spec {G : ProfiniteGrp} {U : Set G}
(UOpen : IsClopen U) (einU : 1 ∈ U) : ((OpenNormalSubgroup_subnhds UOpen einU) : Set G) ⊆ U :=sorry

end ProfiniteGrp
end ProfiniteGrp

end limitofProfinite
