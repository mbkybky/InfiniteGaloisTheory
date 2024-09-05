/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu
-/
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
      rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
      use (canonicalMap P).toFun origin
      constructor
      · have : ((canonicalMap P).toFun origin).1 ∈ J.toSet.pi fJ := fun a a_in_J => by
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
  rw [Set.image_univ, dense_map] at this
  exact Set.range_iff_surjective.mp (id this.symm)

end

section ProfiniteGrp

open scoped Pointwise

theorem exist_open_symm_subnhds {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G] [T2Space G] [CompactSpace G] {W : Set G}
    (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ V : Set G, IsOpen V ∧ V = V⁻¹ ∧ 1 ∈ V ∧ V ⊆ W ∧ W * V ⊆ W := by
  let μ : G × G → G := fun (x, y) ↦ x * y
  have μCont : Continuous μ := continuous_mul
  let μinvW := μ⁻¹' W ∩ (W ×ˢ W)
  have μinvWsubWp : μinvW ⊆ (W ×ˢ W) := Set.inter_subset_right
  have mem_μinvW : ∀ w : W, ((w : G), 1) ∈ μinvW := by
    intro w
    simp only [μinvW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, mul_one, Subtype.coe_prop,
      μ, Subtype.coe_prop, einW, and_self]
  have μinvWOpen : IsOpen μinvW := by
    simp only [μinvW]
    apply IsOpen.inter
    apply μCont.isOpen_preimage W <| IsClopen.isOpen WClopen
    apply IsOpen.prod <;> (apply IsClopen.isOpen WClopen)
  have mem_μinvWOpen : ∀ w : W, ∃ (Uw : Set G) (Vw : Set G), IsOpen Uw ∧ IsOpen Vw ∧ (w : G)  ∈ Uw ∧
    1 ∈ Vw ∧ Uw ×ˢ Vw ⊆ μinvW := by
    intro w
    apply isOpen_prod_iff.mp μinvWOpen w 1 (mem_μinvW w)
  let Uw := fun w ↦ Classical.choose (mem_μinvWOpen w)
  let spec1 := fun w ↦ Classical.choose_spec (mem_μinvWOpen w)
  let Vw' := fun w ↦ Classical.choose (spec1 w)
  let spec2 := fun w ↦ Classical.choose_spec (spec1 w)
  let Vw := fun w ↦ (Vw' w) ∩ (Vw' w)⁻¹
  have spec3 : ∀ w : W, (Uw w) ⊆ W ∧ (Vw' w) ⊆ W :=by
    intro w
    rcases spec2 w with ⟨_,_,_,_,s5⟩
    have : (Uw w) ×ˢ (Vw' w) ⊆ W ×ˢ W := fun g gin => μinvWsubWp (s5 gin)
    rw [Set.prod_subset_prod_iff] at this
    rcases this with _ | empty | empty
    assumption
    repeat
    rw [Set.eq_empty_iff_forall_not_mem] at empty
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
      simp only [Set.iInter_coe_set, Set.mem_iInter, Set.iInter_inv, Set.mem_inv] at h ⊢
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
  · intro a ainmul
    rw [Set.mem_mul] at ainmul
    rcases ainmul with ⟨x,xinW,y,yinInter,xmuly⟩
    have := fincover xinW
    simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at this
    rcases this with ⟨w,winfin,xinU⟩
    simp_rw [Set.mem_iInter] at yinInter
    have yinV := Set.mem_of_mem_inter_left (yinInter w winfin)
    have := Set.mem_of_mem_inter_left <| (spec2 w).2.2.2.2 <| Set.mk_mem_prod xinU yinV
    simpa only [Set.mem_preimage, xmuly, μ] using this

def open_subgroup_subnhds {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G] [T2Space G] [CompactSpace G] {W : Set G}
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
    have : ∀ n : ℕ, ∀ x : G, x ∈ Classical.choose (exist_open_symm_subnhds WClopen einW) ^ n →
      x⁻¹ ∈ Classical.choose (exist_open_symm_subnhds WClopen einW) ^ n := by
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
        dsimp at hyp
        rw [← hyp, DivisionMonoid.mul_inv_rev a b]
        apply Set.mul_mem_mul _ (hk a ha)
        rw [(Classical.choose_spec (exist_open_symm_subnhds WClopen einW)).2.1]
        exact Set.inv_mem_inv.mpr hb
    exact this m x hm

theorem open_subgroup_subnhds_spec {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G] [T2Space G] [CompactSpace G] {W : Set G}
(WClopen : IsClopen W) (einW : 1 ∈ W) :
IsOpen ((open_subgroup_subnhds WClopen einW) : Set G) ∧
((open_subgroup_subnhds WClopen einW) : Set G) ⊆ W := by
  let V := Classical.choose (exist_open_symm_subnhds WClopen einW)
  let ⟨VOpen,_,einV,_,mulVsubW⟩:= Classical.choose_spec (exist_open_symm_subnhds WClopen einW)
  have eqUnion : {x : G | ∃ n : ℕ, x ∈ V ^ n} = ⋃ n ≥ 1 , V ^ n :=by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n,xin⟩
      cases' n with p
      · rw [pow_zero, Set.mem_one] at xin
        use 1
        simp_rw [ge_iff_le, le_refl, pow_one, Set.iUnion_true, xin]
        exact einV
      · use (p + 1)
        simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true, xin]
    · intro h
      simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at h
      rcases h with ⟨n,_,xin⟩
      use n
  constructor
  · show IsOpen {x : G | ∃ n : ℕ, x ∈ V ^ n}
    rw [eqUnion]
    apply isOpen_iUnion
    intro n
    induction' n with n ih
    · simp_rw [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, pow_zero,
        Set.iUnion_of_empty, isOpen_empty]
    · cases' n
      · simp_rw [zero_add, ge_iff_le, le_refl, pow_one, Set.iUnion_true]
        exact VOpen
      · simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true] at ih ⊢
        rw [pow_succ]
        apply IsOpen.mul_left VOpen
  · show {x : G | ∃ n : ℕ, x ∈ V ^ n} ⊆ W
    rw[eqUnion]
    simp_rw [Set.iUnion_subset_iff]
    intro n nge
    have mulVpow: W * V ^ n ⊆ W := by
      induction' n with n ih
      · contradiction
      · cases' n with n
        rw [zero_add, pow_one]
        exact mulVsubW
        simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, true_implies] at ih
        rw [pow_succ, ← mul_assoc]
        have : W * V ^ (n + 1) * V ⊆ W * V := Set.mul_subset_mul_right ih
        apply le_trans this mulVsubW
    apply le_trans _ mulVpow
    intro x xin
    rw [Set.mem_mul]
    use 1, einW, x, xin
    rw [one_mul]


open Pointwise ConjAct MulAction
def openNormalSubgroup_subnhds.aux {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : Set G :=
  Classical.choose ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
      mem_nhds_iff.mpr (by use U))

lemma openNormalSubgroup_subnhds.aux_spec {G : ProfiniteGrp} {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    (1 ∈ (aux UOpen einU) ∧ IsClopen (aux UOpen einU)) ∧ (aux UOpen einU) ⊆ U :=
  Classical.choose_spec ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
        mem_nhds_iff.mpr (by use U))

instance openNormalSubgroup_subnhds.aux_finite {G : ProfiniteGrp} {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    Finite (G ⧸ open_subgroup_subnhds (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1) :=
  have ⟨OOpen, _⟩:= open_subgroup_subnhds_spec (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1
  finite_quotient_of_open_subgroup _ OOpen

open Pointwise ConjAct MulAction
open openNormalSubgroup_subnhds in
def openNormalSubgroup_subnhds {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : OpenNormalSubgroup G where
  toSubgroup :=
    Subgroup.normalCore (open_subgroup_subnhds (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
  isOpen' := by
    letI := finite_quotient_of_open_subgroup
      (open_subgroup_subnhds (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
    set H := (open_subgroup_subnhds (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
    letI : Subgroup.FiniteIndex H := Subgroup.finiteIndex_of_finite_quotient H
    have : IsClosed H.normalCore.carrier := by
      apply TopologicalGroup.normalCore_isClosed
      let H' : OpenSubgroup G := {
        H with
        isOpen' :=
          (open_subgroup_subnhds_spec (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1).1
      }
      exact OpenSubgroup.isClosed H'
    apply TopologicalGroup.finindex_Closed_isOpen
    exact this

theorem OpenNormalSubgroup_subnhds_spec {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : ((openNormalSubgroup_subnhds UOpen einU) : Set G) ⊆ U := by
  have := (Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
    mem_nhds_iff.mpr (by use U)
  let ⟨⟨einW,WClopen⟩,WsubU⟩:= Classical.choose_spec this
  rw [id_eq] at WsubU
  have ⟨_,OsubW⟩:= open_subgroup_subnhds_spec WClopen einW
  have NsubO : ((openNormalSubgroup_subnhds UOpen einU) : Set G) ⊆ open_subgroup_subnhds WClopen einW := by
    show (Subgroup.normalCore (open_subgroup_subnhds WClopen einW) : Set G) ⊆ open_subgroup_subnhds WClopen einW
    simp only [id_eq, SetLike.coe_subset_coe, Subgroup.normalCore_le (open_subgroup_subnhds WClopen einW)]
  apply Set.Subset.trans _ WsubU
  exact Set.Subset.trans NsubO OsubW


theorem injectiveCanonicalMap (P : ProfiniteGrp.{u}) : Function.Injective (canonicalMap P) := by
  show Function.Injective (canonicalMap P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [Subgroup.mem_bot]
  symm
  constructor
  · intro xeq1
    rw [xeq1]
    rfl
  · intro xinKer
    by_contra xne1
    have : (1 : P) ∈ ({x}ᶜ : Set P) := Set.mem_compl_singleton_iff.mpr fun a ↦ xne1 (id (Eq.symm a))
    let H := openNormalSubgroup_subnhds (isOpen_compl_singleton) this
    have xninH: x ∉ H := by
      have := OpenNormalSubgroup_subnhds_spec (isOpen_compl_singleton) this
      exact fun a ↦ this a rfl
    change (canonicalMap P).toMonoidHom x = 1 at xinKer
    unfold canonicalMap at xinKer
    rw [MonoidHom.coe_mk, OneHom.coe_mk] at xinKer
    apply Subtype.val_inj.mpr at xinKer
    let xinH := congrFun xinKer H
    rw [OneMemClass.coe_one, Pi.one_apply] at xinH
    rw[QuotientGroup.eq_one_iff] at xinH
    tauto

theorem bijectiveCanonicalMap (P : ProfiniteGrp.{u}) : Function.Bijective (canonicalMap P) :=
  ⟨injectiveCanonicalMap P,surjectiveCanonicalMap P⟩

def equiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) : P ≃ (ofFiniteGrpLimit (diagramOfProfiniteGrp P)) where
  toFun := (canonicalMap P)
  invFun := Function.surjInv (surjectiveCanonicalMap P)
  left_inv := Function.leftInverse_surjInv <| bijectiveCanonicalMap P
  right_inv := Function.rightInverse_surjInv <| surjectiveCanonicalMap P

def continuousMulEquiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) : ContinuousMulEquiv P (ofFiniteGrpLimit (diagramOfProfiniteGrp P)) := {
  equiv_FiniteGrpLimit P with
  map_mul' := (canonicalMap P).map_mul'
  continuous_toFun := by
    rw [Equiv.toFun_as_coe]
    apply map_continuous P.canonicalMap
  continuous_invFun := by
    rw [Equiv.invFun_as_coe]
    apply Continuous.continuous_symm_of_equiv_compact_to_t2 <| map_continuous P.canonicalMap
}

end ProfiniteGrp
end ProfiniteGrp

end limitofProfinite
