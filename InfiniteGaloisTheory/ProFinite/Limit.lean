/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Youle Fang, Yi Song, Xuchun Li, Yongle Hu
-/
import InfiniteGaloisTheory.ProFinite.Basic
import InfiniteGaloisTheory.MissingLemmas.Subgroup

/-!

# The projective limit of finite groups is profinite

# A profinite Group is the projective limit of finite groups

## Main definitions and results

* `FiniteGrp.limit` : the concretely constructed limit of finite group as a subgroup of the product

* `ofFiniteGrpLimit`: direct limit of finite groups is a profinite group

* Verify that the constructed limit satisfies the universal property.

In a profinite group `P` :

* `QuotientOpenNormalSubgroup` : The functor mapping open normal subgroup of `P` to
  the quotient group of it (finite by previous lemmas).

* `CanonicalMap` : The continuous homomorphism from `P` to the limit of the quotient group of
  open normal subgroup ordered by inclusion of the open normal subgroup.

* `CanonicalMap_surjective` : The CanonicalMap is surjective,
  by proving the range of it is dense and closed.

* `openNormalSubgroup_subnhd` : For any open neighborhood of `1` there is an open normal subgroup
  contained in it.

* `CanonicalMap_injective` : The CanonicalMap is injective.

-/

suppress_compilation

universe u v

open CategoryTheory Topology

section Profiniteoflimit

/- In this section, we prove that the projective limit of finite groups is profinite-/

universe w w'

variable {J : Type v} [Category.{w, v} J] (F : J ⥤ FiniteGrp.{max v w'})

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

instance (j : J) : TopologicalSpace (F.obj j) := ⊥

instance (j : J) : DiscreteTopology (F.obj j) := ⟨rfl⟩

instance (j : J) : TopologicalGroup (F.obj j) := {}

namespace FiniteGrp

/-- Concretely constructing the limit of topological group-/

def limit : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[simp]
lemma mem_limit (x : Π j : J, F.obj j) : x ∈ limit F ↔
  ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j := Iff.rfl

instance : CompactSpace (limit F) := ClosedEmbedding.compactSpace (f := (limit F).subtype)
  { induced := rfl
    inj := Subgroup.subtype_injective _
    isClosed_range := by
      classical
      let S ⦃i j : J⦄ (π : i ⟶ j) : Set (Π j : J, F.obj j) := {x | F.map π (x i) = x j}
      have hS ⦃i j : J⦄ (π : i ⟶ j) : IsClosed (S π) := by
        simp only [S]
        rw [← isOpen_compl_iff, isOpen_pi_iff]
        rintro x (hx : ¬ _)
        simp only [Set.mem_setOf_eq] at hx
        refine ⟨{i, j}, fun i => {x i}, ?_⟩
        simp only [Finset.mem_singleton, isOpen_discrete, Set.mem_singleton_iff, and_self,
          implies_true, Finset.coe_singleton, Set.singleton_pi, true_and]
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_pi, Set.singleton_pi,
          Set.mem_inter_iff, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
          Set.mem_compl_iff, Set.mem_setOf_eq] at hy ⊢
        rwa [hy.1, hy.2]
      have eq : Set.range (limit F).subtype = ⋂ (i : J) (j : J) (π : i ⟶ j), S π := by
        ext x
        simp only [Subgroup.coeSubtype, Subtype.range_coe_subtype, SetLike.mem_coe, mem_limit,
          Set.mem_setOf_eq, Set.mem_iInter]
        tauto
      rw [eq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun π => hS π }

end FiniteGrp

namespace ProfiniteGrp

def ofFiniteGrpLimit : ProfiniteGrp := .of (FiniteGrp.limit F)

/-- verify that the limit constructed above satisfies the universal property-/
@[simps]
def ofFiniteGrpLimitCone : Limits.Cone (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  pt := ofFiniteGrpLimit F
  π :=
  { app := fun j => {
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        dsimp
        have triv : Continuous fun x : ((Functor.const J).obj (ofFiniteGrpLimit F)).obj j ↦ x.1 :=
          continuous_iff_le_induced.mpr fun U a => a
        have : Continuous fun (x1 : (j : J) → F.obj j) ↦ x1 j := continuous_apply j
        exact this.comp triv
    }
    naturality := by
      intro i j f
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x ↦ (x.2 f).symm
  }

@[simps]
def ofFiniteGrpLimitConeIsLimit : Limits.IsLimit (ofFiniteGrpLimitCone F) where
  lift cone := {
    toFun := fun pt ↦
      { val := fun j => (cone.π.1 j) pt
        property := fun i j πij ↦ by
          have := cone.π.2 πij
          simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
            Category.id_comp, Functor.comp_map] at this
          simp only [Functor.const_obj_obj, Functor.comp_obj, this]
          rfl }
    map_one' := by
      apply SetCoe.ext
      simp only [Functor.const_obj_obj, Functor.comp_obj, OneMemClass.coe_one, Pi.one_apply,
        OneHom.toFun_eq_coe, OneHom.coe_mk, id_eq, Functor.const_obj_map, Functor.comp_map,
        MonoidHom.toOneHom_coe, MonoidHom.coe_mk, eq_mpr_eq_cast, cast_eq, map_one]
      rfl
    map_mul' := fun x y => by
      apply SetCoe.ext
      simp only [Functor.const_obj_obj, Functor.comp_obj, OneMemClass.coe_one, Pi.one_apply,
        OneHom.toFun_eq_coe, OneHom.coe_mk, id_eq, Functor.const_obj_map, Functor.comp_map,
        MonoidHom.toOneHom_coe, MonoidHom.coe_mk, eq_mpr_eq_cast, cast_eq, map_mul]
      rfl
    continuous_toFun := by
      dsimp
      apply continuous_induced_rng.mpr
      show  Continuous (fun pt ↦ (fun j ↦ (cone.π.app j) pt))
      apply continuous_pi
      intro j
      exact (cone.π.1 j).continuous_toFun
  }
  fac cone j := by
    dsimp
    ext pt
    simp only [comp_apply]
    rfl
  uniq := by
    dsimp
    intro cone g hyp
    ext pt
    refine Subtype.ext <| funext fun j => ?_
    show _ = cone.π.app _ _
    rw [←hyp j]
    rfl

instance : Limits.HasLimit (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  exists_limit := Nonempty.intro
    { cone := ofFiniteGrpLimitCone F
      isLimit := ofFiniteGrpLimitConeIsLimit F
    }

end ProfiniteGrp

end Profiniteoflimit

section limitofProfinite

/-In this section, we prove that a profinite Group is the projective limit of finite groups-/

namespace ProfiniteGrp

section

def QuotientOpenNormalSubgroup (P : ProfiniteGrp) :
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
      X.toSubgroup Y.toSubgroup Z.toSubgroup (.id _) (.id _)
      (Subgroup.comap_id Y.toSubgroup ▸ leOfHom f)
      (Subgroup.comap_id Z.toSubgroup ▸ leOfHom g)).symm
  }


def CanonicalMap (P : ProfiniteGrp.{u}) : P ⟶ ofFiniteGrpLimit (QuotientOpenNormalSubgroup P) where
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
    apply isOpen_iUnion
    intro i
    apply isOpen_iUnion
    intro ih
    rw [QuotientGroup.preimage_mk_eq_coset]
    exact IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out' i)

theorem denseCanonicalMap (P : ProfiniteGrp.{u}) : Dense $ Set.range (CanonicalMap P) :=
  dense_iff_inter_open.mpr
    fun U hUO hUNonempty => (by
      rcases hUNonempty with ⟨uDefault, uDefaultSpec⟩
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
      use (CanonicalMap P).toFun origin
      constructor
      · rw [←hsv]
        apply h_ok_and_in_s.2
        exact fun a a_in_J => by
          let M_to_Na : m ⟶ a := (iInf_le subg ⟨a, a_in_J⟩).hom
          rw [← (P.CanonicalMap.toFun origin).property M_to_Na]
          show (P.QuotientOpenNormalSubgroup.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
          rw [horigin, hspc M_to_Na]
          exact (h_ok_and_in_s.1 a a_in_J).2
      · exact ⟨origin, rfl⟩
    )

theorem CanonicalMap_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (CanonicalMap P) := by
  have : IsClosedMap P.CanonicalMap := P.CanonicalMap.continuous_toFun.isClosedMap
  haveI compact_s: IsCompact (Set.univ : Set P) := CompactSpace.isCompact_univ
  have : IsClosed (P.CanonicalMap '' Set.univ) := this _ $ IsCompact.isClosed compact_s
  have dense_map := Dense.closure_eq $ denseCanonicalMap P
  apply closure_eq_iff_isClosed.mpr at this
  rw [Set.image_univ, dense_map] at this
  exact Set.range_iff_surjective.mp (id this.symm)

end

section

open scoped Pointwise

theorem open_symm_subnbhs_of_one {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G]
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
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
  have mem_μinvWOpen : ∀ w : W, ∃ (Uw : Set G) (Vw : Set G), IsOpen Uw ∧ IsOpen Vw
      ∧ (w : G)  ∈ Uw ∧ 1 ∈ Vw ∧ Uw ×ˢ Vw ⊆ μinvW := by
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
    · constructor
      · apply Set.mem_inter s4
        simp only [Set.mem_inv, inv_one, s4]
      constructor
      · ext
        simp only [Vw, Set.mem_inter_iff, Set.mem_inv, Set.inter_inv, inv_inv, And.comm]
      intro x ⟨xV,_⟩
      exact s7 xV
  have cover : W ⊆ ⋃ w : W, Uw w := by
    intro x xinW
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    use x, xinW
    exact (spec2 ⟨x,xinW⟩).2.2.1
  rcases IsCompact.elim_finite_subcover (IsClosed.isCompact (IsClopen.isClosed WClopen))
    _ (fun w ↦ (spec2 w).1) cover with ⟨fin,fincover⟩
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
  simp only [isOpen_biInter_finset fun w _ ↦ (spec4 w).1, true_and]
  constructor
  · ext x
    constructor <;>
    · intro h
      simp only [Set.iInter_coe_set, Set.mem_iInter, Set.iInter_inv, Set.mem_inv] at h ⊢
      intro w winW winfin
      specialize h w winW winfin
      rw[(spec4 ⟨w,winW⟩).2.2.1]
      simp only [Set.mem_inv, inv_inv, h]
  constructor
  · simp_rw [Set.mem_iInter]
    intro w _
    exact (spec4 w).2.1
  constructor
  · intro x xinInter
    simp_rw [Set.mem_iInter] at xinInter
    specialize xinInter w0 w0.prop
    exact (spec4 w0).2.2.2 xinInter
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

lemma eqUnion_pow {G : Type*} [Group G] {V : Set G} (h : 1 ∈ V) : {x : G | ∃ n : ℕ, x ∈ V ^ n} = ⋃ n ≥ 1 , V ^ n :=by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n,xin⟩
      cases' n with p
      · rw [pow_zero, Set.mem_one] at xin
        use 1
        simp_rw [ge_iff_le, le_refl, pow_one, Set.iUnion_true, xin]
        exact h
      · use (p + 1)
        simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true, xin]
    · intro h
      simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at h
      rcases h with ⟨n,_,xin⟩
      use n

def OpenSubgroup_subnhds_of_one {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G]
    [T2Space G] [CompactSpace G] {W : Set G}
    (WClopen : IsClopen W) (einW : 1 ∈ W) : OpenSubgroup G where
  carrier := {x : G | ∃ n : ℕ, x ∈ Classical.choose (open_symm_subnbhs_of_one WClopen einW) ^ n}
  mul_mem':= by
    rintro a b ⟨na, hna⟩ ⟨nb, hnb⟩
    simp only [Set.mem_setOf_eq] at *
    use na + nb
    rw [pow_add]
    exact Set.mul_mem_mul hna hnb
  one_mem':= by
    simp only [Set.mem_setOf_eq]
    use 1
    rw [pow_one]
    exact (Classical.choose_spec (open_symm_subnbhs_of_one WClopen einW)).2.2.1
  inv_mem':= by
    simp only [Set.mem_setOf_eq, forall_exists_index] at *
    intro x m hm
    use m
    have : ∀ n : ℕ, ∀ x : G, x ∈ Classical.choose (open_symm_subnbhs_of_one WClopen einW) ^ n →
      x⁻¹ ∈ Classical.choose (open_symm_subnbhs_of_one WClopen einW) ^ n := by
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
        rw [(Classical.choose_spec (open_symm_subnbhs_of_one WClopen einW)).2.1]
        exact Set.inv_mem_inv.mpr hb
    exact this m x hm
  isOpen' := by
    let V := Classical.choose (open_symm_subnbhs_of_one WClopen einW)
    let ⟨VOpen,_,einV,_,_⟩:= Classical.choose_spec (open_symm_subnbhs_of_one WClopen einW)
    show IsOpen {x : G | ∃ n : ℕ, x ∈ V ^ n}
    rw [eqUnion_pow einV]
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

theorem OpenSubgroup_subnhds_of_one_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [T2Space G] [CompactSpace G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ((OpenSubgroup_subnhds_of_one WClopen einW) : Set G) ⊆ W := by
  let V := Classical.choose (open_symm_subnbhs_of_one WClopen einW)
  let ⟨_,_,einV,_,mulVsubW⟩:= Classical.choose_spec (open_symm_subnbhs_of_one WClopen einW)
  show {x : G | ∃ n : ℕ, x ∈ V ^ n} ⊆ W
  rw[eqUnion_pow einV]
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

open Pointwise

namespace openNormalSubgroup_subnhds

def aux {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : Set G :=
  Classical.choose ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
      mem_nhds_iff.mpr (by use U))

lemma aux_spec {G : ProfiniteGrp} {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    (1 ∈ (aux UOpen einU) ∧ IsClopen (aux UOpen einU)) ∧ (aux UOpen einU) ⊆ U :=
  Classical.choose_spec ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
        mem_nhds_iff.mpr (by use U))

instance aux_finite {G : ProfiniteGrp} {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    Finite (G⧸(OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1).1)
    :=
  finite_quotient_of_open_subgroup _
    (OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1).isOpen'

end openNormalSubgroup_subnhds

open Pointwise
open openNormalSubgroup_subnhds in
def openNormalSubgroup_subnhds {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : OpenNormalSubgroup G where
  toSubgroup := Subgroup.normalCore
    (OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
  isOpen' := by
    set H := (OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
    letI := finite_quotient_of_open_subgroup H.1
    letI : Subgroup.FiniteIndex H := Subgroup.finiteIndex_of_finite_quotient H.1
    apply TopologicalGroup.finindex_Closed_isOpen
    apply TopologicalGroup.normalCore_isClosed
    exact OpenSubgroup.isClosed H

theorem openNormalSubgroup_subnhds_of_one_spec {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : ((openNormalSubgroup_subnhds UOpen einU) : Set G) ⊆ U := by
  have := (Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
    mem_nhds_iff.mpr (by use U)
  let ⟨⟨einW,WClopen⟩,WsubU⟩ := Classical.choose_spec this
  rw [id_eq] at WsubU
  have OsubW := OpenSubgroup_subnhds_of_one_spec WClopen einW
  exact Set.Subset.trans (Set.Subset.trans
    (Subgroup.normalCore_le (OpenSubgroup_subnhds_of_one WClopen einW).1) OsubW) WsubU

theorem CanonicalMap_injective (P : ProfiniteGrp.{u}) : Function.Injective (CanonicalMap P) := by
  show Function.Injective (CanonicalMap P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  have : (1 : P) ∈ ({x}ᶜ : Set P) :=
    Set.mem_compl_singleton_iff.mpr fun a ↦ xne1 (id (Eq.symm a))
  let H := openNormalSubgroup_subnhds (isOpen_compl_singleton) this
  have xninH : x ∉ H := fun a ↦
    (openNormalSubgroup_subnhds_of_one_spec (isOpen_compl_singleton) this) a rfl
  have xinKer : (CanonicalMap P).toMonoidHom x = 1 := h
  simp only [CanonicalMap, MonoidHom.coe_mk, OneHom.coe_mk] at xinKer
  apply Subtype.val_inj.mpr at xinKer
  have xinH := congrFun xinKer H
  rw [OneMemClass.coe_one, Pi.one_apply, QuotientGroup.eq_one_iff] at xinH
  exact xninH xinH

theorem bijectiveCanonicalMap (P : ProfiniteGrp.{u}) : Function.Bijective (CanonicalMap P) :=
  ⟨CanonicalMap_injective P, CanonicalMap_surjective P⟩

def equiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) :
    P ≃ (ofFiniteGrpLimit (QuotientOpenNormalSubgroup P)) where
  toFun := (CanonicalMap P)
  invFun := Function.surjInv (CanonicalMap_surjective P)
  left_inv := Function.leftInverse_surjInv <| bijectiveCanonicalMap P
  right_inv := Function.rightInverse_surjInv <| CanonicalMap_surjective P

def continuousMulEquiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) :
    ContinuousMulEquiv P (ofFiniteGrpLimit (QuotientOpenNormalSubgroup P)) := {
  (Continuous.homeoOfEquivCompactToT2 (f := equiv_FiniteGrpLimit P) P.CanonicalMap.continuous_toFun)
  with
  map_mul' := (CanonicalMap P).map_mul'
}

end

end ProfiniteGrp

end limitofProfinite
