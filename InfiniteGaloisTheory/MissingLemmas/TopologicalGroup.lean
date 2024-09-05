/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import InfiniteGaloisTheory.MissingLemmas.Subgroup

universe u v

section

variable (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G] (H : Type v) [Group H] [TopologicalSpace H] [TopologicalGroup H]

structure ContinuousMulEquiv extends MulEquiv G H , Homeomorph G H

namespace ContinuousMulEquiv

variable {G} {H}

def symm (cme : ContinuousMulEquiv G H) : ContinuousMulEquiv H G := {
  cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun
  }

def trans {K : Type*} [Group K] [TopologicalSpace K] [TopologicalGroup K]
    (cme1 : ContinuousMulEquiv G H) (cme2 : ContinuousMulEquiv H K) : ContinuousMulEquiv G K := {
  cme1.toMulEquiv.trans cme2.toMulEquiv with
  continuous_toFun :=
    let this := Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
    this
  continuous_invFun :=
    let this := Continuous.comp cme1.continuous_invFun cme2.continuous_invFun
    this
  }

end ContinuousMulEquiv

end

section

variable (G : Type u) [Group G] [TopologicalSpace G]

@[ext]
structure ClosedSubgroup extends Subgroup G where
  isClosed' : IsClosed carrier

namespace ClosedSubgroup

variable {G} in
theorem toSubgroup_injective : Function.Injective
  (ClosedSubgroup.toSubgroup : ClosedSubgroup G → Subgroup G) :=
  fun A B h => by
  ext
  rw [h]

instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

instance : PartialOrder (ClosedSubgroup G) := inferInstance

instance instInfClosedSubgroup : Inf (ClosedSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : ClosedSubgroup G → Set G) fun _ _ => rfl

end ClosedSubgroup

@[ext]
structure OpenNormalSubgroup extends OpenSubgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

namespace OpenNormalSubgroup

instance (H : OpenNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

variable {G} in
theorem toSubgroup_injective : Function.Injective
  (fun H => H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G → Subgroup G) :=
  fun A B h => by
  ext
  dsimp at h
  rw [h]

instance : SetLike (OpenNormalSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

instance : SubgroupClass (OpenNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

instance : Coe (OpenNormalSubgroup G) (Subgroup G) where
  coe := fun H => H.toOpenSubgroup.toSubgroup

instance : PartialOrder (OpenNormalSubgroup G) := inferInstance

instance instInfClosedSubgroup : Inf (OpenNormalSubgroup G) :=
  ⟨fun U V => ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : OpenNormalSubgroup G → Set G) fun _ _ => rfl

end OpenNormalSubgroup

open scoped Pointwise

namespace TopologicalGroup

lemma normalCore_isClosed [TopologicalGroup G] (H : Subgroup G) (h : IsClosed (H : Set G)) :
  IsClosed (H.normalCore : Set G) := by
  rw [Subgroup.normalCore_eq_iInf_conjAct]
  push_cast
  apply isClosed_iInter
  intro g
  convert IsClosed.preimage (TopologicalGroup.continuous_conj (ConjAct.ofConjAct g⁻¹)) h
  ext t
  exact Set.mem_smul_set_iff_inv_smul_mem

lemma finindex_Closed_isOpen [TopologicalGroup G] (H : Subgroup G) [Subgroup.FiniteIndex H]
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
    use ⟨QuotientGroup.mk (s := H) x, this.symm⟩, (Quotient.out' (QuotientGroup.mk (s := H) x))⁻¹ * x
    simp only [SetLike.mem_coe, smul_eq_mul, mul_inv_cancel_left, and_true]
    apply QuotientGroup.eq.mp <| QuotientGroup.out_eq' (QuotientGroup.mk (s := H) x)
  · rcases h with ⟨S,⟨y,hS⟩,mem⟩
    simp only [← hS, f] at mem
    rcases mem with ⟨h,hh,eq⟩
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    by_contra mH
    simp only [← eq, ne_eq, smul_eq_mul] at mH
    absurd y.2.symm
    rw [←QuotientGroup.out_eq' y.1]
    apply QuotientGroup.eq.mpr
    simp only [inv_one, ne_eq, one_mul, (Subgroup.mul_mem_cancel_right H hh).mp mH]

end TopologicalGroup

end

namespace Homeomorph

protected lemma TotallyDisconnectedSpace {A : Type u} [TopologicalSpace A]
  {B : Type v} [TopologicalSpace B] (e : Homeomorph A B) [tdc : TotallyDisconnectedSpace A] :
  TotallyDisconnectedSpace B :=
  (totallyDisconnectedSpace_iff B).mpr
    ((Homeomorph.range_coe e) ▸
      ((Embedding.isTotallyDisconnected_range (Homeomorph.embedding e)).mpr tdc))

end Homeomorph

def Pi.profinite {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)
