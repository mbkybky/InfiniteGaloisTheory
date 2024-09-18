/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Youle Fang, Yi Song, Xuchun Li, Yongle Hu
-/
import InfiniteGaloisTheory.New.ProfiniteGrp.Basic'
import InfiniteGaloisTheory.New.MissingLemmas.Compact
import InfiniteGaloisTheory.New.MissingLemmas.Subgroup
import InfiniteGaloisTheory.New.MissingLemmas.ClosedSubgroup
import InfiniteGaloisTheory.New.MissingLemmas.OpenNormalSubgroup

/-!

# The projective limit of finite groups is profinite

# A profinite Group is the projective limit of finite groups

## Main definitions and results

* `FiniteGrp.limit` : the concretely constructed limit of finite group as a subgroup of the product

* `ofFiniteGrpLimit`: direct limit of finite groups is a profinite group

* Verify that the constructed limit satisfies the universal property.

In a profinite group `P` :

* `QuotientOpenNormalSubgroup` : The functor that maps open normal subgroup of `P` to
  the quotient group of it (which is finite, as shown by previous lemmas).

* `CanonicalQuotientMap` : The continuous homomorphism from `P` to the limit of the quotient group
  of open normal subgroup ordered by inclusion of the open normal subgroup.

* `canonicalQuotientMap_surjective` : The `CanonicalQuotientMap` is surjective, proven by
  demonstrating that its range is dense and closed.

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained within it.

* `canonicalQuotientMap_injective` : The `CanonicalQuotientMap` is injective. This is proven by
  showing that for any element not equal to one, the image of it on the coordinate of
  the open normal subgroup that doesn't contain it is not equal to 1, thus not in the kernel.

* `ContinuousMulEquivLimitQuotientOpenNormalSubgroup` : The `CanonicalQuotientMap` can serve as a
  `ContinuousMulEquiv`, with the continuity of other side given by
  `Continuous.homeoOfEquivCompactToT2`.

-/

suppress_compilation

universe u v

open CategoryTheory Topology TopologicalGroup

section Profiniteoflimit

/- In this section, we prove that the projective limit of finite groups is profinite-/

universe w w'

variable {J : Type v} [Category.{w, v} J] (F : J ⥤ FiniteGrp.{max v w'})

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

instance (j : J) : TopologicalSpace (F.obj j) := ⊥

instance (j : J) : DiscreteTopology (F.obj j) := ⟨rfl⟩

instance (j : J) : TopologicalGroup (F.obj j) := {}

namespace FiniteGrp

/-- Concretely constructing the limit of topological group as a subgroup of the product group. -/
def limit : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[simp]
lemma mem_limit (x : Π j : J, F.obj j) : x ∈ limit F ↔
  ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j := Iff.rfl

lemma limit_closed_in_product : IsClosed ((limit F) : Set (Π j : J, F.obj j)) := by
  classical
  let S ⦃i j : J⦄ (π : i ⟶ j) : Set (Π j : J, F.obj j) := {x | F.map π (x i) = x j}
  have hS ⦃i j : J⦄ (π : i ⟶ j) : IsClosed (S π) := by
    simp only [S, ← isOpen_compl_iff, isOpen_pi_iff]
    rintro x (hx : ¬ _)
    refine ⟨{i, j}, fun i => {x i}, ?_⟩
    simp only [Finset.mem_singleton, isOpen_discrete, Set.mem_singleton_iff, and_self,
      implies_true, Finset.coe_singleton, Set.singleton_pi, true_and]
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_pi, Set.singleton_pi,
      Set.mem_inter_iff, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq] at hy ⊢
    rwa [hy.1, hy.2]
  have eq : limit F = ⋂ (i : J) (j : J) (π : i ⟶ j), S π := by
    ext x
    simp only [Subgroup.coeSubtype, Subtype.range_coe_subtype, SetLike.mem_coe, mem_limit,
      Set.mem_setOf_eq, Set.mem_iInter]
    tauto
  exact eq ▸ isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun π => hS π

instance : CompactSpace (limit F) := isCompact_iff_compactSpace.mp <|
  IsClosed.isCompact <| limit_closed_in_product F

end FiniteGrp

namespace ProfiniteGrp

/-- Making the direct limit of `FiniteGrp` into a `ProfiniteGrp`. -/
def ofFiniteGrpLimit : ProfiniteGrp := .of (FiniteGrp.limit F)

/-- Verify that the limit constructed above exist projections to the `FiniteGrps`
that are compatible with the morphisms between them. -/
def ofFiniteGrpLimitCone : Limits.Cone (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  pt := ofFiniteGrpLimit F
  π :=
  { app := fun j => {
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a => a)
    }
    naturality := by
      intro i j f
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm
  }

@[simp]
lemma ofFiniteGrpLimitCone_pt : (ProfiniteGrp.ofFiniteGrpLimitCone F).pt =
    ProfiniteGrp.ofFiniteGrpLimit F := rfl

@[simp, nolint simpNF]
lemma ofFiniteGrpLimitCone_π_app_apply  (j : J) (x : ↑(((CategoryTheory.Functor.const J).obj
    (ProfiniteGrp.ofFiniteGrpLimit F)).obj j).toProfinite.toTop) :
    ((ProfiniteGrp.ofFiniteGrpLimitCone F).π.app j) x = x.1 j := rfl

/-- Verify that the limit constructed above satisfies the universal property. -/
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
    continuous_toFun :=  continuous_induced_rng.mpr
      (continuous_pi (fun j => (cone.π.1 j).continuous_toFun))
  }
  fac cone j := by
    ext pt
    simp only [comp_apply]
    rfl
  uniq := by
    intro cone g hyp
    ext pt
    refine Subtype.ext <| funext fun j => ?_
    show _ = cone.π.app _ _
    rw [←hyp j]
    rfl

@[simp, nolint simpNF]
lemma ofFiniteGrpLimitConeIsLimit_lift_toFun_coe (j : J) (cone : Limits.Cone
  (F ⋙ forget₂ FiniteGrp.{max v w'} ProfiniteGrp.{max v w'})) (pt : ↑cone.pt.toProfinite.toTop) :
  (((ProfiniteGrp.ofFiniteGrpLimitConeIsLimit F).lift cone) pt).val j = (cone.π.app j) pt := rfl

instance : Limits.HasLimit (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  exists_limit := Nonempty.intro
    { cone := ofFiniteGrpLimitCone F
      isLimit := ofFiniteGrpLimitConeIsLimit F }

end ProfiniteGrp

end Profiniteoflimit

section limitofProfinite

namespace ProfiniteGrp

/-- The open normal subgroup contained in an open nhd of `1`
in a compact totallydisconnected topological group. -/
noncomputable def OpenNormalSubgroupSubOpenNhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) : OpenNormalSubgroup G :=
  let h := Classical.choose_spec ((Filter.HasBasis.mem_iff'
    ((nhds_basis_clopen (1 : G))) U ).mp <| mem_nhds_iff.mpr (by use U))
  OpenNormalSubgroupSubClopenNhdsOfOne h.1.2 h.1.1

theorem openNormalSubgroupSubOpenNhdsOfOne_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    ((OpenNormalSubgroupSubOpenNhdsOfOne UOpen einU) : Set G) ⊆ U :=
  let ⟨⟨einW,WClopen⟩,WsubU⟩ := Classical.choose_spec <| (Filter.HasBasis.mem_iff'
    ((nhds_basis_clopen (1 : G))) U ).mp <| mem_nhds_iff.mpr (by use U)
  fun _ b ↦ WsubU (openNormalSubgroupSubClopenNhdsOfOne_spec WClopen einW b)

section

/-- Define the functor from OpenNormalSubgroup of a profinite group to the quotient group of it as
  a `FiniteGrp` -/
def QuotientOpenNormalSubgroup (P : ProfiniteGrp) :
    OpenNormalSubgroup P ⥤ FiniteGrp := {
    obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
    map := fun {H K} fHK => QuotientGroup.map H.toSubgroup K.toSubgroup (.id _) <|
        Subgroup.comap_id (N := P) K ▸ leOfHom fHK
    map_id := fun H => by
      simp only [QuotientGroup.map_id]
      rfl
    map_comp := fun {X Y Z} f g => (QuotientGroup.map_comp_map
      X.toSubgroup Y.toSubgroup Z.toSubgroup (.id _) (.id _)
      (Subgroup.comap_id Y.toSubgroup ▸ leOfHom f)
      (Subgroup.comap_id Z.toSubgroup ▸ leOfHom g)).symm
  }

/-- Defining the canonical projection from a profinite group to the limit of the quotient groups as a
  subgroup of the product space -/
def CanonicalQuotientMap (P : ProfiniteGrp.{u}) : P ⟶
    ofFiniteGrpLimit (QuotientOpenNormalSubgroup P) where
  toFun := fun p => {
    val := fun H => QuotientGroup.mk p
    property := fun A B _ => rfl
  }
  map_one' := Subtype.val_inj.mp (by ext H; rfl)
  map_mul' := fun x y => Subtype.val_inj.mp (by ext H; rfl)
  continuous_toFun := by
    apply continuous_induced_rng.mpr (continuous_pi _)
    intro H
    dsimp
    apply Continuous.mk
    intro s _
    rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
    apply isOpen_iUnion
    intro i
    apply isOpen_iUnion
    intro _
    convert IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out' i)
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    nth_rw 1 [←QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
    symm
    apply Set.mem_smul_set_iff_inv_smul_mem

theorem canonicalQuotientMap_dense (P : ProfiniteGrp.{u}) : Dense <|
     Set.range (CanonicalQuotientMap P) :=
  dense_iff_inter_open.mpr
    fun U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩ => (by
      let uMemPiOpen := isOpen_pi_iff.mp hsO
      simp_rw [← hsv] at uDefaultSpec
      rw [Set.mem_preimage] at uDefaultSpec
      specialize uMemPiOpen _ uDefaultSpec
      rcases uMemPiOpen with ⟨J, fJ, h_ok_and_in_s⟩
      let M := iInf (fun (j : J) => j.1.1.1)
      haveI hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
      haveI hMOpen : IsOpen (M : Set P) := by
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
      let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
      rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
      use (CanonicalQuotientMap P).toFun origin
      constructor
      · rw [←hsv]
        apply h_ok_and_in_s.2
        exact fun a a_in_J => by
          let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
          rw [← (P.CanonicalQuotientMap.toFun origin).property M_to_Na]
          show (P.QuotientOpenNormalSubgroup.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
          rw [horigin, hspc M_to_Na]
          exact (h_ok_and_in_s.1 a a_in_J).2
      · exact ⟨origin, rfl⟩
    )

theorem canonicalQuotientMap_surjective (P : ProfiniteGrp.{u}) :
    Function.Surjective (CanonicalQuotientMap P) := by
  have : IsClosedMap P.CanonicalQuotientMap := P.CanonicalQuotientMap.continuous_toFun.isClosedMap
  haveI compact_s: IsCompact (Set.univ : Set P) := CompactSpace.isCompact_univ
  have : IsClosed (P.CanonicalQuotientMap '' Set.univ) := this _ <| IsCompact.isClosed compact_s
  apply closure_eq_iff_isClosed.mpr at this
  rw [Set.image_univ, Dense.closure_eq <| canonicalQuotientMap_dense P] at this
  exact Set.range_iff_surjective.mp (id this.symm)

theorem canonicalQuotientMap_injective (P : ProfiniteGrp.{u}) :
    Function.Injective (CanonicalQuotientMap P) := by
  show Function.Injective (CanonicalQuotientMap P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  have : (1 : P) ∈ ({x}ᶜ : Set P) := Set.mem_compl_singleton_iff.mpr fun a => xne1 (id (Eq.symm a))
  let H := OpenNormalSubgroupSubOpenNhdsOfOne (isOpen_compl_singleton) this
  have xninH : x ∉ H := fun a =>
    (openNormalSubgroupSubOpenNhdsOfOne_spec (isOpen_compl_singleton) this) a rfl
  have xinKer : (CanonicalQuotientMap P).toMonoidHom x = 1 := h
  simp only [CanonicalQuotientMap, MonoidHom.coe_mk, OneHom.coe_mk] at xinKer
  apply Subtype.val_inj.mpr at xinKer
  have xinH := congrFun xinKer H
  rw [OneMemClass.coe_one, Pi.one_apply, QuotientGroup.eq_one_iff] at xinH
  exact xninH xinH

/-- Make the equivilence into a ContinuousMulEquiv -/
noncomputable def ContinuousMulEquivLimitQuotientOpenNormalSubgroup (P : ProfiniteGrp.{u}) :
    ContinuousMulEquiv P (ofFiniteGrpLimit (QuotientOpenNormalSubgroup P)) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨canonicalQuotientMap_injective P, canonicalQuotientMap_surjective P⟩)
    P.CanonicalQuotientMap.continuous_toFun)
  with
  map_mul' := (CanonicalQuotientMap P).map_mul'
  }

end

end ProfiniteGrp

end limitofProfinite
