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
import Mathlib.Topology.Algebra.Group.Basic
import InfiniteGaloisTheory.MissingLemmas.Topology
import InfiniteGaloisTheory.MissingLemmas.Subgroup

/-!

# Category of Profinite Groups

We say `G` is a profinite group if it is a topological group which is compact and totally
disconnected.

## Main definitions and results

* `ProfiniteGrp` is the type of profinite groups.
* `FiniteGrp` is the type of finite groups.
* `limitOfFiniteGrp`: direct limit of finite groups is a profinite group

-/

suppress_compilation

universe u v

open CategoryTheory Topology

@[pp_with_univ]
structure ProfiniteGrp where
  toProfinite : Profinite
  [isGroup : Group toProfinite]
  [isTopologicalGroup : TopologicalGroup toProfinite]

@[pp_with_univ]
structure FiniteGrp where
  toGrp : Grp
  [isFinite : Finite toGrp]

namespace FiniteGrp

instance : CoeSort FiniteGrp.{u} (Type u) where
  coe G := G.toGrp

instance : Category FiniteGrp := InducedCategory.category FiniteGrp.toGrp

instance : ConcreteCategory FiniteGrp := InducedCategory.concreteCategory FiniteGrp.toGrp

instance (G : FiniteGrp) : Group G := inferInstanceAs $ Group G.toGrp

instance (G : FiniteGrp) : Finite G := G.isFinite

instance (G H : FiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs $ FunLike (G →* H) G H

instance (G H : FiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs $ MonoidHomClass (G →* H) G H

def of (G : Type u) [Group G] [Finite G] : FiniteGrp where
  toGrp := Grp.of G
  isFinite := ‹_›

def ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) : of X ⟶ of Y :=
  Grp.ofHom f

lemma ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) (x : X) :
  ofHom f x = f x :=
  rfl

end FiniteGrp

namespace ProfiniteGrp

instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

instance (G : ProfiniteGrp) : Group G := G.isGroup

instance (G : ProfiniteGrp) : TopologicalGroup G := G.isTopologicalGroup

def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  isGroup := ‹_›
  isTopologicalGroup := ‹_›

def ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] : ProfiniteGrp where
  toProfinite := G
  isGroup := inferInstanceAs $ Group G
  isTopologicalGroup := inferInstanceAs $ TopologicalGroup G

def Pi.profiniteGrp {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Pi.profinite fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).isGroup
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

instance : Category ProfiniteGrp where
  Hom A B := ContinuousMonoidHom A B
  id A := ContinuousMonoidHom.id A
  comp f g := ContinuousMonoidHom.comp g f

instance (G H : ProfiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs $ FunLike (ContinuousMonoidHom G H) G H

instance (G H : ProfiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs $ MonoidHomClass (ContinuousMonoidHom G H) G H

instance (G H : ProfiniteGrp) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs $ ContinuousMapClass (ContinuousMonoidHom G H) G H

instance : ConcreteCategory ProfiniteGrp where
  forget :=
  { obj := fun G => G
    map := fun f => f.toFun }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, id_eq] at h ⊢
        exact DFunLike.ext _ _ $ fun x => congr_fun h x }

def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

def ofHomeoMulEquivProfiniteGrp {G : ProfiniteGrp.{u}} (H : Type v) [TopologicalSpace H] [Group H]
    [TopologicalGroup H] (e : ContinuousMulEquiv G H) : ProfiniteGrp.{v} :=
  letI : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  letI : TotallyDisconnectedSpace G := Profinite.instTotallyDisconnectedSpaceαTopologicalSpaceToTop
  letI : TotallyDisconnectedSpace H := Homeomorph.TotallyDisconnectedSpace e.toHomeomorph
  .of H

def ofClosedSubgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : ProfiniteGrp :=
  letI : CompactSpace H := ClosedEmbedding.compactSpace (f := H.subtype)
    { induced := rfl
      inj := H.subtype_injective
      isClosed_range := by simpa }
  of H

instance : CategoryTheory.HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f => ⟨f, by continuity⟩ }

section

universe w w'

variable {J : Type v} [Category.{w, v} J] (F : J ⥤ FiniteGrp.{max v w'})

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

instance (j : J) : TopologicalSpace (F.obj j) := ⊥

instance (j : J) : DiscreteTopology (F.obj j) := ⟨rfl⟩

instance (j : J) : TopologicalGroup (F.obj j) := {}

/-Concretely constructing the limit of topological group-/

def G_ : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp
  inv_mem' h _ _ π := by simp [h π]

@[simp]
lemma mem_G_ (x : Π j : J, F.obj j) : x ∈ G_ F ↔ ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j :=
  Iff.rfl

instance : CompactSpace (G_ F) := ClosedEmbedding.compactSpace (f := (G_ F).subtype)
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
      have eq : Set.range (G_ F).subtype = ⋂ (i : J) (j : J) (π : i ⟶ j), S π := by
        ext x
        simp only [Subgroup.coeSubtype, Subtype.range_coe_subtype, SetLike.mem_coe, mem_G_,
          Set.mem_setOf_eq, Set.mem_iInter]
        tauto
      rw [eq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun π => hS π }

def limitOfFiniteGrp : ProfiniteGrp := of (G_ F)

/-- verify that the limit constructed above satisfies the universal property-/
@[simps]
def limitOfFiniteGrpCone : Limits.Cone (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  pt := limitOfFiniteGrp F
  π :=
  { app := fun j => {
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        dsimp
        have triv : Continuous fun x : ((Functor.const J).obj (limitOfFiniteGrp F)).obj j ↦ x.1 :=
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
def limitOfFiniteGrpConeIsLimit : Limits.IsLimit (limitOfFiniteGrpCone F) where
  lift cone := {
    toFun := fun pt ↦
      { val := fun j => (cone.π.1 j) pt
        property := fun i j πij ↦ by
          have := cone.π.2 πij
          simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
            Category.id_comp, Functor.comp_map] at this
          simp [this]
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
    change _ = cone.π.app _ _
    rw [←hyp j]
    rfl

instance : Limits.HasLimit (F ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  exists_limit := Nonempty.intro
    { cone := limitOfFiniteGrpCone F
      isLimit := limitOfFiniteGrpConeIsLimit F
    }

end

section

open scoped Pointwise

def finite_quotient_of_open_subgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : Finite (G ⧸ H) := by
  obtain h := @CompactSpace.isCompact_univ G _ _
  rw [isCompact_iff_finite_subcover] at h
  have : (Set.univ : Set G) ⊆ ⋃ (i : G), i • (H : Set G) :=
    fun g _ => Set.mem_iUnion_of_mem g ⟨1, ⟨one_mem H, by simp⟩⟩
  specialize h (fun x : G => x • (H : Set G)) (IsOpen.smul hH) this
  obtain ⟨t, ht⟩ := h
  let f : t → (G ⧸ H) := fun ⟨x, _⟩ => QuotientGroup.mk x
  apply Finite.of_surjective f
  intro x
  have : x.out' ∈ ⋃ i ∈ t, i • (H : Set G) := ht trivial
  simp only [Set.mem_iUnion] at this
  choose i hi hii using this
  use ⟨i, hi⟩
  rw [mem_leftCoset_iff] at hii
  have : i⁻¹ * Quotient.out' x ∈ H := hii
  rw [← @QuotientGroup.eq _ _ H i x.out'] at this
  show Quotient.mk'' i = x
  rw [Eq.symm (QuotientGroup.out_eq' x)]
  exact this

def finiteIndex_of_open_subgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : H.FiniteIndex :=
  haveI : Finite (G ⧸ H) := finite_quotient_of_open_subgroup H hH
  Subgroup.finiteIndex_of_finite_quotient H



def diagramOfProfiniteGrp (P : ProfiniteGrp) :
  {x : Subgroup P | x.Normal ∧ IsOpen (x: Set P)} ⥤ FiniteGrp := {
    obj := fun ⟨H, _, hH⟩ =>
      letI : Finite (P ⧸ H) := finite_quotient_of_open_subgroup H hH
      FiniteGrp.of (P ⧸ H)
    map := fun {H K} fHK =>
      let ⟨H, _, _⟩ := H
      let ⟨K, _, _⟩ := K
      QuotientGroup.map H K (.id _) $ Subgroup.comap_id K ▸ leOfHom fHK
    map_id := by
      intro ⟨x, _, _⟩
      simp only [QuotientGroup.map_id, id_apply]
      exact rfl
    map_comp := by
      intro ⟨x, _, _⟩ ⟨y, _, _⟩ ⟨z, _, _⟩ f g
      simp only [MonoidHom.id]
      sorry
  }

open Pointwise
lemma preimage_mk_eq_coset {G : Type u} [Group G] {H : Subgroup G} (i : G ⧸ H) : QuotientGroup.mk ⁻¹' {i} = (Quotient.out' i) • ↑H := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hxi
    rw [← hxi]
    let ⟨t, ht⟩ := QuotientGroup.mk_out'_eq_mul H x
    rw [ht]
    use t⁻¹
    simp only [SetLike.mem_coe, inv_mem_iff, SetLike.coe_mem, smul_eq_mul, mul_inv_cancel_right, and_self]
  intro ⟨t, hht, ht⟩
  simp only [smul_eq_mul] at ht
  have : i = QuotientGroup.mk (Quotient.out' i) := by exact Eq.symm (QuotientGroup.out_eq' i)
  rw [this]
  refine QuotientGroup.eq.mpr ?h.mpr.a
  rw [← ht]; simp only [mul_inv_rev, inv_mul_cancel_right, inv_mem_iff]; exact hht

def canonicalMap (P : ProfiniteGrp) : P ⟶ limitOfFiniteGrp (diagramOfProfiniteGrp P) where
  toFun := fun p => {
    val := fun ⟨H, _, _⟩ => QuotientGroup.mk p
    property := fun ⟨A, _, _⟩ ⟨B, _, _⟩ _ => by
      unfold diagramOfProfiniteGrp; rfl
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
    rw [preimage_mk_eq_coset]
    exact IsOpen.leftCoset hHO (Quotient.out' i)


#check canonicalMap
#check instTopologicalSpaceSubtype

theorem denseCanonicalMap (P : ProfiniteGrp) : Dense (canonicalMap P).range.carrier := dense_iff_inter_open.mpr
  fun U hUO hUNonempty => (by
    unfold limitOfFiniteGrp at U
    unfold ProfiniteGrp.of at U
    simp only [Set.coe_setOf, Set.mem_setOf_eq, CompHausLike.coe_of] at U
    unfold G_ at U
    let uDefault := hUNonempty.some
    let uDefaultSpec := hUNonempty.some_mem

    let NormalOpenType := { x : Subgroup P // x.Normal ∧ IsOpen (x: Set P) }
    -- let piFun := (j : NormalOpenType) → (P.diagramOfProfiniteGrp.obj j).toGrp
    -- let property_piFun : piFun → Prop := fun x ↦ ∀ (a : NormalOpenType) (b : NormalOpenType) (π : a ⟶ b), (P.diagramOfProfiniteGrp.map π) (x a) = x b
    rcases hUO with ⟨s, hsO, hsv⟩
    simp_rw [Set.coe_setOf] at s

    let uMemPiOpen := isOpen_pi_iff.mp hsO
    simp_rw [← hsv] at uDefaultSpec
    rw [Set.mem_preimage] at uDefaultSpec
    specialize uMemPiOpen _ uDefaultSpec
    rcases uMemPiOpen with ⟨J, fJ, h⟩

    let subg: ∀ j : J, Subgroup P := fun ⟨j, hj⟩ => j.val
    haveI subgNormal: ∀ j : J, (subg j).Normal := fun ⟨j, hj⟩ => j.property.1
    let M := iInf subg
    letI hM : M.Normal := Subgroup.normal_iInf_normal subgNormal
    letI hMOpen : IsOpen (M : Set P) := by
      unfold_let
      sorry
    sorry
  )

end

end ProfiniteGrp
