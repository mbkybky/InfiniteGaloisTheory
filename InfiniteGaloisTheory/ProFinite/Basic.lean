/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu
-/

import InfiniteGaloisTheory.ProFinite.Defs

/-!

# Basic properties of Profinite Groups

* `ofContinuousMulEquivProfiniteGrp` : If a topological group have a two-sided continuous
  isomorphism to a profinite group then it is profinite as well.

* `ofClosedSubgroup` : The closed subgroup of a profinite group is profinite.

* `finiteIndex_of_open_subgroup` : An open subgroup of a profinite group has finite index.

-/

suppress_compilation

universe u v

open CategoryTheory Topology

namespace ProfiniteGrp

def ofContinuousMulEquivProfiniteGrp {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
    [Group H] [TopologicalGroup H] (e : ContinuousMulEquiv G H) : ProfiniteGrp.{v} :=
  letI : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  letI : TotallyDisconnectedSpace G := Profinite.instTotallyDisconnectedSpaceαTopologicalSpaceToTop
  letI : TotallyDisconnectedSpace H := Homeomorph.TotallyDisconnectedSpace e.toHomeomorph
  .of H

def ofClosedSubgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : ProfiniteGrp :=
  letI : CompactSpace H := ClosedEmbedding.compactSpace (f := H.subtype)
    { induced := rfl
      inj := H.subtype_injective
      isClosed_range := by simpa only [Subgroup.coeSubtype, Subtype.range_coe_subtype] }
  of H

open scoped Pointwise

def finite_quotient_of_open_subgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : Finite (G ⧸ H) := by
  obtain h := @CompactSpace.isCompact_univ G _ _
  rw [isCompact_iff_finite_subcover] at h
  have : (Set.univ : Set G) ⊆ ⋃ (i : G), i • (H : Set G) :=
    fun g _ => Set.mem_iUnion_of_mem g ⟨1, ⟨one_mem H, by simp only [smul_eq_mul, mul_one]⟩⟩
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

lemma finiteIndex_of_open_subgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : H.FiniteIndex :=
  haveI : Finite (G ⧸ H) := finite_quotient_of_open_subgroup H hH
  Subgroup.finiteIndex_of_finite_quotient H

end ProfiniteGrp

section CompactSubgroup

structure CompactSubgroup (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
 extends Subgroup G where
  to_compact : CompactSpace carrier

namespace CompactSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G]

instance : SetLike (CompactSubgroup G) G where
  coe H := H.carrier
  coe_injective' := by
    rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
    simp only [mk.injEq, Subgroup.mk.injEq, Submonoid.mk.injEq, Subsemigroup.mk.injEq, imp_self]

instance : SubgroupClass (CompactSubgroup G) G where
  mul_mem := mul_mem (S := Subgroup G)
  one_mem x := one_mem x.toSubgroup
  inv_mem := inv_mem (S := Subgroup G)

instance (H : CompactSubgroup G) : CompactSpace H := H.to_compact

instance (H : CompactSubgroup G) : CompactSpace H.toSubgroup := H.to_compact

--instance (H : CompactSubgroup G) : Subgroup G := H.toSubgroup

instance (H : CompactSubgroup G) : Group H := inferInstance

variable [TotallyDisconnectedSpace G]

def toProfiniteGrp (H : CompactSubgroup G) : ProfiniteGrp.{u} := .of H.toSubgroup


def ofClosedSubgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) : CompactSubgroup G := {
  H with to_compact := isCompact_iff_compactSpace.mp (IsClosed.isCompact hH)
  }

def compactSubgroup_of_closed (H : CompactSubgroup G) : IsClosed (H : Set G) :=
  IsCompact.isClosed (isCompact_iff_compactSpace.mpr H.to_compact)

end CompactSubgroup

end CompactSubgroup
