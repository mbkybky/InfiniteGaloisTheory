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

--abbrev OpenNormalSubgroup (G : ProfiniteGrp) := {H : Subgroup G // H.Normal ∧ IsOpen (H : Set G)}

def diagramOfProfiniteGrp (P : ProfiniteGrp) :
  OpenNormalSubgroup P ⥤ FiniteGrp := {
    obj := fun H =>
      letI := H.isNormal'
      letI : Finite (P ⧸ H.toSubgroup) := finite_quotient_of_open_subgroup
        H.toSubgroup H.toOpenSubgroup.isOpen'
      FiniteGrp.of (P ⧸ H.toSubgroup)
    map := fun {H K} fHK => QuotientGroup.map H.toSubgroup K.toSubgroup (.id _) $
        Subgroup.comap_id (N := P) K ▸ leOfHom fHK
    map_id := fun H => by
      simp only [QuotientGroup.map_id]
      rfl
    map_comp := fun {X Y Z} f g => (QuotientGroup.map_comp_map
      X.toSubgroup Y.toSubgroup Z.toSubgroup (.id _) (.id _) (Subgroup.comap_id Y.toSubgroup ▸ leOfHom f)
        (Subgroup.comap_id Z.toSubgroup ▸ leOfHom g)).symm
  }


def canonicalMap (P : ProfiniteGrp.{u}) : P ⟶ ofFiniteGrpLimit (diagramOfProfiniteGrp P) where
  toFun := fun p => {
    val := fun H => QuotientGroup.mk p
    property := fun A B _ => rfl
  }
  map_one' := Subtype.val_inj.mp (by ext H; rfl)
  map_mul' := fun x y => Subtype.val_inj.mp (by ext H; rfl)
  continuous_toFun := by
    dsimp
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro H
    dsimp
    apply Continuous.mk
    intro s _
    rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
    apply isOpen_iUnion; intro i
    apply isOpen_iUnion; intro ih
    rw [QuotientGroup.preimage_mk_eq_coset]
    exact IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out' i)

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
      let subg: J → Subgroup P := fun j => j.1.1.1
      haveI subgNormal: ∀ j : J, (subg j).Normal := fun j => j.1.isNormal'
      let M := iInf subg
      haveI hM : M.Normal := Subgroup.normal_iInf_normal subgNormal
      haveI hMOpen : IsOpen (M : Set P) := by
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
      let m : OpenNormalSubgroup P := {
        M with
        isOpen' := hMOpen
      }
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
  let μ : W × W → G := fun (x, y) ↦ x * y
  have μCont : Continuous μ :=by continuity
  have mem_μinvW : ∀ w : W, (w, ⟨1, einW⟩) ∈ μ⁻¹' W := by
    intro w
    simp only [Set.mem_preimage, mul_one, Subtype.coe_prop, μ]
  have μinvWOpen : IsOpen (μ⁻¹' W) := μCont.isOpen_preimage W <| IsClopen.isOpen WClopen
  have mem_μinvWOpen : ∀ w : W, ∃ Uw Vw, IsOpen Uw ∧ IsOpen Vw ∧ w ∈ Uw ∧
    ⟨1, einW⟩ ∈ Vw ∧ Uw ×ˢ Vw ⊆ (μ⁻¹' W) := by
    intro w
    apply isOpen_prod_iff.mp μinvWOpen w ⟨1, einW⟩ (mem_μinvW w)
  clear μCont mem_μinvW μinvWOpen

  let Uw := fun w ↦ Classical.choose (mem_μinvWOpen w)
  let spec1 := fun w ↦ Classical.choose_spec (mem_μinvWOpen w)
  let Vw' := fun w ↦ Classical.choose (spec1 w)
  let spec2 := fun w ↦ Classical.choose_spec (spec1 w)
  let Vw : W → Set W := fun w ↦
  {x : W | x ∈ Vw' w ∧ (x : G) ∈ (Vw' w : Set G)⁻¹ }


  have : ∀ w : W, IsOpen (Uw w) ∧ IsOpen (Vw w) ∧
    w ∈ (Uw w) ∧ ⟨1, einW⟩ ∈ (Vw w) ∧ (Uw w) ×ˢ (Vw w) ⊆ (μ ⁻¹' W) ∧
    ∀ v ∈ (Vw w : Set G) , v⁻¹ ∈ (Vw w : Set G) := by
    intro w
    rcases spec2 w with ⟨s1,s2,s3,s4,s5⟩
    constructor ; exact s1
    constructor
    · apply IsOpen.and s2
      have : IsOpen (Vw' w : Set G) := IsOpen.trans s2 (IsClopen.isOpen WClopen)
      have : IsOpen (Vw' w : Set G)⁻¹ := IsOpen.inv this
      have := (IsOpen.isOpenMap_subtype_val (IsClopen.isOpen WClopen))


      sorry
    constructor ; exact s3
    constructor ; simp only [Set.mem_inv, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Set.mem_setOf_eq, s4, inv_one, einW, exists_const, and_self, Vw]
    constructor
    · intro (w1,w2) hw
      unfold_let Vw at hw
      simp only [Set.mem_prod, Set.mem_setOf_eq] at hw
      have : (w1,w2) ∈ (Uw w) ×ˢ (Vw' w) := by
        simp only [Set.mem_prod, hw.1, hw.2, and_self]
      exact s5 this
    · intro v vinVw
      have : v ∈ (Vw' w : Set G) ∧ (v : G) ∈ (Vw' w : Set G)⁻¹ :=sorry
      sorry





  have cover : W ⊆ ⋃ w : W, Uw w := by
    intro w winW
    simp only [Set.mem_iUnion, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    use w, winW ,winW
    exact (spec2 ⟨w,winW⟩).2.2.1

  have :True :=sorry



  sorry

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
