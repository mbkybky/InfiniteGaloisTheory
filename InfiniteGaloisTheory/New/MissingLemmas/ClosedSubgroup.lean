/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Topology.Algebra.Group.Basic
import InfiniteGaloisTheory.MissingLemmas.Subgroup --to be changed
import Mathlib.GroupTheory.Index

/-!
# Open subgroups of a topological groups

This files builds the SemilatticeInf `ClosedSubgroup G` of closed subgroups in a
topological group `G`, and its additive version `ClosedAddSubgroup`.

# Main definitions and results

* `normalCore_isClosed` : The `normalCore` of a closed subgroup is closed.

*  `finiteindex_closedSubgroup_isOpen` : A closed subgroup with finite index is open.

-/

section

universe u v

/-- The type of open subgroups of a topological group. -/
@[ext]
structure ClosedSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Subgroup G where
  isClosed' : IsClosed carrier

/-- The type of open subgroups of a topological group. -/
@[ext]
structure ClosedAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G] extends
    AddSubgroup G where
  isClosed' : IsClosed carrier

attribute [to_additive] ClosedSubgroup

attribute [coe] ClosedSubgroup.toSubgroup ClosedAddSubgroup.toAddSubgroup

namespace ClosedSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G]

variable {G} in
@[to_additive]
theorem toSubgroup_injective : Function.Injective
  (ClosedSubgroup.toSubgroup : ClosedSubgroup G → Subgroup G) :=
  fun A B h => by
  ext
  rw [h]

@[to_additive]
instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

@[to_additive]
instance : PartialOrder (ClosedSubgroup G) := inferInstance

@[to_additive]
instance instInfClosedSubgroup : Inf (ClosedSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]
instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : ClosedSubgroup G → Set G) fun _ _ => rfl

end ClosedSubgroup

open scoped Pointwise

namespace TopologicalGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]

lemma normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) :
  IsClosed (H.normalCore : Set G) := by
  rw [Subgroup.normalCore_eq_iInf_conjAct]
  push_cast
  apply isClosed_iInter
  intro g
  convert IsClosed.preimage (TopologicalGroup.continuous_conj (ConjAct.ofConjAct g⁻¹)) h
  ext t
  exact Set.mem_smul_set_iff_inv_smul_mem

@[to_additive]
lemma finiteindex_closedSubgroup_isOpen (H : Subgroup G) [H.FiniteIndex]
  (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  apply isClosed_compl_iff.mp
  letI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex H
  let f : {x : (G ⧸ H) // x ≠ QuotientGroup.mk 1} → Set G :=
    fun x => ((Quotient.out' x.1) : G) • (H : Set G)
  have close : IsClosed (⋃ x, f x) :=
    isClosed_iUnion_of_finite (fun x => IsClosed.smul h (Quotient.out' x.1))
  convert close
  ext x
  constructor
  all_goals intro h
  · simp only [Set.mem_compl_iff, SetLike.mem_coe] at h
    have : QuotientGroup.mk 1 ≠ QuotientGroup.mk (s := H) x := by
      apply QuotientGroup.eq.not.mpr
      simpa only [inv_one, one_mul, ne_eq]
    simp only [ne_eq, Set.mem_iUnion]
    use ⟨QuotientGroup.mk (s := H) x, this.symm⟩,
      (Quotient.out' (QuotientGroup.mk (s := H) x))⁻¹ * x
    simp only [SetLike.mem_coe, smul_eq_mul, mul_inv_cancel_left, and_true]
    exact QuotientGroup.eq.mp <| QuotientGroup.out_eq' (QuotientGroup.mk (s := H) x)
  · rcases h with ⟨S,⟨y,hS⟩,mem⟩
    simp only [← hS, f] at mem
    rcases mem with ⟨h,hh,eq⟩
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    by_contra mH
    simp only [← eq, ne_eq, smul_eq_mul] at mH
    absurd y.2.symm
    rw [← QuotientGroup.out_eq' y.1]
    apply QuotientGroup.eq.mpr
    simp only [inv_one, ne_eq, one_mul, (Subgroup.mul_mem_cancel_right H hh).mp mH]

end TopologicalGroup

end
