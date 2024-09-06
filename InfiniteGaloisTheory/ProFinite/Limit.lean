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
        have triv : Continuous fun x : ((Functor.const J).obj (ofFiniteGrpLimit F)).obj j => x.1 :=
          continuous_iff_le_induced.mpr fun U a => a
        have : Continuous fun (x1 : (j : J) → F.obj j) => x1 j := continuous_apply j
        exact this.comp triv
    }
    naturality := by
      intro i j f
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm
  }

@[simps]
def ofFiniteGrpLimitConeIsLimit : Limits.IsLimit (ofFiniteGrpLimitCone F) where
  lift cone := {
    toFun := fun pt =>
      { val := fun j => (cone.π.1 j) pt
        property := fun i j πij => by
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
      show  Continuous (fun pt => (fun j => (cone.π.app j) pt))
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

section

variable {G : Type*} [Group G]

def symm (V : Set G) : Set G := V ∩ V⁻¹

lemma symm_spec (V : Set G) : (symm V) = (symm V)⁻¹ := by
  ext
  simp only [symm, Set.mem_inter_iff, Set.mem_inv, Set.inter_inv, inv_inv, and_comm]

lemma inter_symm {α : Type*}
    (S : Set α) (V : α → Set G) : ⋂ a ∈ S, symm (V a) = (⋂ a ∈ S, symm (V a))⁻¹ := by
  ext x
  constructor <;>
  · intro h
    simp only [Set.iInter_coe_set, Set.mem_iInter, Set.iInter_inv, Set.mem_inv] at h ⊢
    intro s hs
    rw [symm_spec]
    simp only [Set.mem_inv, inv_inv, h s hs]

def μinvW
    (W : Set G) : Set (G × G) :=
  let μ : G × G → G := fun (x, y) => x * y
  μ⁻¹' W ∩ (W ×ˢ W)

lemma μinvW_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) : IsOpen (μinvW W) := by
  let μ : G × G → G := fun (x, y) => x * y
  have μCont : Continuous μ := continuous_mul
  simp only [μinvW]
  apply IsOpen.inter (μCont.isOpen_preimage W <| IsClopen.isOpen WClopen) _
  apply IsOpen.prod <;> (apply IsClopen.isOpen WClopen)

lemma mem_μinvW
    {W : Set G} (einW : 1 ∈ W) (w : W) : ((w : G), 1) ∈ μinvW W := by
  simp only [μinvW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, mul_one, Subtype.coe_prop,
      Subtype.coe_prop, einW, and_self]

def nhds_side_w [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)

def nhds_side_1' [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)

lemma nhds_side_w_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : IsOpen (nhds_side_w WClopen einW w)
    :=
  (Classical.choose_spec <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)).1

lemma nhds_side_1'_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : IsOpen (nhds_side_1' WClopen einW w)
    :=
  (Classical.choose_spec <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)).2.1

lemma w_mem_nhds_side_w [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    w.1 ∈ (nhds_side_w WClopen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)).2.2.1

lemma one_mem_nhds_side_1 [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    1 ∈ (nhds_side_1' WClopen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)).2.2.2.1

lemma nhds_side_mul_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    (nhds_side_w WClopen einW w) ×ˢ (nhds_side_1' WClopen einW w) ⊆ μinvW W :=
  (Classical.choose_spec <| Classical.choose_spec <|
    isOpen_prod_iff.mp (μinvW_open WClopen) w 1 (mem_μinvW einW w)).2.2.2.2

def nhds_side_1 [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : Set G :=
  symm (nhds_side_1' WClopen einW w)

lemma nhds_side_1_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : IsOpen (nhds_side_1 WClopen einW w)
    := by
  simp only [nhds_side_1, symm]
  apply IsOpen.inter (nhds_side_1'_open WClopen einW w)
    (IsOpen.inv (nhds_side_1'_open WClopen einW w))

lemma One_mem_nhds_side_1 [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) : 1 ∈ (nhds_side_1 WClopen einW w)
    := by
  simp only [nhds_side_1, symm, Set.mem_inter_iff, Set.mem_inv, inv_one, and_self]
  exact (one_mem_nhds_side_1 WClopen einW w)

lemma nhds_side_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    (nhds_side_w WClopen einW w) ⊆ W ∧ (nhds_side_1' WClopen einW w) ⊆ W:= by
  have μinvWsubWp : μinvW W ⊆ (W ×ˢ W) := Set.inter_subset_right
  have := Set.Subset.trans (nhds_side_mul_sub WClopen einW w) μinvWsubWp
  rw [Set.prod_subset_prod_iff] at this
  rcases this with h | e1 | e2
  · exact h
  · absurd e1
    exact ne_of_mem_of_not_mem' (w_mem_nhds_side_w WClopen einW w) fun a ↦ a
  · absurd e2
    exact ne_of_mem_of_not_mem' (one_mem_nhds_side_1 WClopen einW w) fun a ↦ a

lemma nhds_side_w_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    (nhds_side_w WClopen einW w) ⊆ W := (nhds_side_sub WClopen einW w).1

lemma nhds_side_1_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) (w : W) :
    (nhds_side_1 WClopen einW w) ⊆ W := by
  simp only [nhds_side_1, symm]
  exact Set.Subset.trans Set.inter_subset_left (nhds_side_sub WClopen einW w).2

lemma nhds_side_w_cover [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ w : W, (nhds_side_w WClopen einW w) := by
  intro x xinW
  simp only [Set.iUnion_coe_set, Set.mem_iUnion]
  exact ⟨x, xinW, (w_mem_nhds_side_w WClopen einW ⟨x, xinW⟩)⟩

def open_symm_subnhds_of_one_index [TopologicalSpace G]  [TopologicalGroup G]
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Finset W :=
  Classical.choose (IsCompact.elim_finite_subcover (IsClosed.isCompact (IsClopen.isClosed WClopen))
    _ (fun (w : W) => (nhds_side_w_open WClopen einW w)) (nhds_side_w_cover WClopen einW))

lemma open_symm_subnhds_of_one_index_spec [TopologicalSpace G]  [TopologicalGroup G]
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ i ∈ (open_symm_subnhds_of_one_index WClopen einW), nhds_side_w WClopen einW i :=
  Classical.choose_spec (IsCompact.elim_finite_subcover (IsClosed.isCompact
  (IsClopen.isClosed WClopen)) _ (fun (w : W) => (nhds_side_w_open WClopen einW w))
  (nhds_side_w_cover WClopen einW))

def open_symm_subnhds_of_one [TopologicalSpace G]  [TopologicalGroup G]
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Set G :=
  ⋂ w ∈ (open_symm_subnhds_of_one_index WClopen einW) , nhds_side_1 WClopen einW w

namespace open_symm_subnhds_of_one

variable [TopologicalSpace G]  [TopologicalGroup G]

lemma isopen
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    IsOpen (open_symm_subnhds_of_one WClopen einW) :=
  isOpen_biInter_finset (fun w _ => nhds_side_1_open WClopen einW w)

lemma symm
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    (open_symm_subnhds_of_one WClopen einW) = (open_symm_subnhds_of_one WClopen einW)⁻¹ := by
  simp only [open_symm_subnhds_of_one, nhds_side_1]
  apply inter_symm

lemma one_mem
    [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    1 ∈ (open_symm_subnhds_of_one WClopen einW) := by
  simp only [open_symm_subnhds_of_one, Set.mem_iInter]
  exact fun w _ => One_mem_nhds_side_1 WClopen einW w

lemma mul_sub
  [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W * (open_symm_subnhds_of_one WClopen einW) ⊆ W := by
  intro a ainmul
  rcases ainmul with ⟨x,xinW,y,yinInter,xmuly⟩
  have fincover := open_symm_subnhds_of_one_index_spec WClopen einW
  have := fincover xinW
  simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at this
  rcases this with ⟨w,winfin,xinU⟩
  simp only [open_symm_subnhds_of_one, Set.iUnion_coe_set, Set.iInter_coe_set, Set.mem_iInter
    ] at yinInter
  have yinV := Set.mem_of_mem_inter_left (yinInter w w.2 winfin)
  have := Set.mem_of_mem_inter_left <| nhds_side_mul_sub WClopen einW w <| Set.mk_mem_prod xinU yinV
  simpa only [Set.mem_preimage, xmuly] using this

lemma sub
  [T2Space G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
   (open_symm_subnhds_of_one WClopen einW) ⊆ W := by
  apply Set.Subset.trans _ (mul_sub WClopen einW)
  exact Set.subset_mul_right (open_symm_subnhds_of_one WClopen einW) einW

end open_symm_subnhds_of_one

end

lemma eqUnion_pow {G : Type*} [Group G] {V : Set G} (h : 1 ∈ V) : {x : G | ∃ n : ℕ, x ∈ V ^ n} =
    ⋃ n ≥ 1 , V ^ n :=by
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
  carrier := {x : G | ∃ n : ℕ, x ∈ (open_symm_subnhds_of_one WClopen einW) ^ n}
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
    exact ProfiniteGrp.open_symm_subnhds_of_one.one_mem WClopen einW
  inv_mem':= by
    simp only [Set.mem_setOf_eq, forall_exists_index] at *
    intro x m hm
    use m
    have : ∀ n : ℕ, ∀ x ∈ (open_symm_subnhds_of_one WClopen einW) ^ n,
      x⁻¹ ∈ (open_symm_subnhds_of_one WClopen einW) ^ n := by
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
        rw [ProfiniteGrp.open_symm_subnhds_of_one.symm WClopen einW]
        exact Set.inv_mem_inv.mpr hb
    exact this m x hm
  isOpen' := by
    set V := (open_symm_subnhds_of_one WClopen einW)
    let VOpen := ProfiniteGrp.open_symm_subnhds_of_one.isopen WClopen einW
    let einV := ProfiniteGrp.open_symm_subnhds_of_one.one_mem WClopen einW
    show IsOpen {x : G | ∃ n : ℕ, x ∈ V ^ n}
    rw [eqUnion_pow einV]
    apply isOpen_iUnion
    intro n
    induction' n with n ih
    · simp_rw [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, pow_zero,
        Set.iUnion_of_empty, isOpen_empty]
    · cases' n
      · simp_rw [zero_add, ge_iff_le, le_refl, pow_one, Set.iUnion_true, VOpen]
      · simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true] at ih ⊢
        rw [pow_succ]
        exact IsOpen.mul_left VOpen

theorem OpenSubgroup_subnhds_of_one_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [T2Space G] [CompactSpace G]
    {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ((OpenSubgroup_subnhds_of_one WClopen einW) : Set G) ⊆ W := by
  let V := (open_symm_subnhds_of_one WClopen einW)
  let einV := ProfiniteGrp.open_symm_subnhds_of_one.one_mem WClopen einW
  let mulVsubW := ProfiniteGrp.open_symm_subnhds_of_one.mul_sub WClopen einW
  show {x : G | ∃ n : ℕ, x ∈ V ^ n} ⊆ W
  simp_rw [eqUnion_pow einV, Set.iUnion_subset_iff]
  intro n nge
  have mulVpow: W * V ^ n ⊆ W := by
    induction' n with n ih
    · contradiction
    · cases' n with n
      · rw [zero_add, pow_one]
        exact mulVsubW
      · simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, true_implies] at ih
        rw [pow_succ, ← mul_assoc]
        exact le_trans (Set.mul_subset_mul_right ih) mulVsubW
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
noncomputable def openNormalSubgroup_subnhds {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : OpenNormalSubgroup G where
  toSubgroup := Subgroup.normalCore
    (OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
  isOpen' := by
    set H := (OpenSubgroup_subnhds_of_one (aux_spec UOpen einU).1.2 (aux_spec UOpen einU).1.1)
    letI := finite_quotient_of_open_subgroup H.1
    letI : Subgroup.FiniteIndex H := Subgroup.finiteIndex_of_finite_quotient H.1
    apply TopologicalGroup.finindex_Closed_isOpen
    exact TopologicalGroup.normalCore_isClosed _ H.1 <| OpenSubgroup.isClosed H


theorem openNormalSubgroup_subnhds_of_one_spec {G : ProfiniteGrp} {U : Set G}
(UOpen : IsOpen U) (einU : 1 ∈ U) : ((openNormalSubgroup_subnhds UOpen einU) : Set G) ⊆ U := by
  have := (Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
    mem_nhds_iff.mpr (by use U)
  let ⟨⟨einW,WClopen⟩,WsubU⟩ := Classical.choose_spec this
  rw [id_eq] at WsubU
  exact Set.Subset.trans (Set.Subset.trans (Subgroup.normalCore_le
    (OpenSubgroup_subnhds_of_one WClopen einW).1)
    (OpenSubgroup_subnhds_of_one_spec WClopen einW)) WsubU

theorem CanonicalMap_injective (P : ProfiniteGrp.{u}) : Function.Injective (CanonicalMap P) := by
  show Function.Injective (CanonicalMap P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  have : (1 : P) ∈ ({x}ᶜ : Set P) :=
    Set.mem_compl_singleton_iff.mpr fun a => xne1 (id (Eq.symm a))
  let H := openNormalSubgroup_subnhds (isOpen_compl_singleton) this
  have xninH : x ∉ H := fun a =>
    (openNormalSubgroup_subnhds_of_one_spec (isOpen_compl_singleton) this) a rfl
  have xinKer : (CanonicalMap P).toMonoidHom x = 1 := h
  simp only [CanonicalMap, MonoidHom.coe_mk, OneHom.coe_mk] at xinKer
  apply Subtype.val_inj.mpr at xinKer
  have xinH := congrFun xinKer H
  rw [OneMemClass.coe_one, Pi.one_apply, QuotientGroup.eq_one_iff] at xinH
  exact xninH xinH

theorem bijectiveCanonicalMap (P : ProfiniteGrp.{u}) : Function.Bijective (CanonicalMap P) :=
  ⟨CanonicalMap_injective P, CanonicalMap_surjective P⟩

noncomputable def equiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) :
    P ≃ (ofFiniteGrpLimit (QuotientOpenNormalSubgroup P)) where
  toFun := (CanonicalMap P)
  invFun := Function.surjInv (CanonicalMap_surjective P)
  left_inv := Function.leftInverse_surjInv <| bijectiveCanonicalMap P
  right_inv := Function.rightInverse_surjInv <| CanonicalMap_surjective P

noncomputable def continuousMulEquiv_FiniteGrpLimit (P : ProfiniteGrp.{u}) :
    ContinuousMulEquiv P (ofFiniteGrpLimit (QuotientOpenNormalSubgroup P)) := {
  (Continuous.homeoOfEquivCompactToT2 (f := equiv_FiniteGrpLimit P) P.CanonicalMap.continuous_toFun)
  with
  map_mul' := (CanonicalMap P).map_mul'
}

end

end ProfiniteGrp

end limitofProfinite
