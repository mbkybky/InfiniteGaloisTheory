/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.Profinite.Basic

universe u v

section

variable (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G] (H : Type v) [Group H] [TopologicalSpace H] [TopologicalGroup H]

structure ContinuousMulEquiv extends MulEquiv G H , Homeomorph G H

namespace ContinuousMulEquiv

def symm (cme : ContinuousMulEquiv G H) : ContinuousMulEquiv H G := {
  cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun
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

instance instSemilatticeInfOpenSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : ClosedSubgroup G → Set G) fun _ _ => rfl

end ClosedSubgroup

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
