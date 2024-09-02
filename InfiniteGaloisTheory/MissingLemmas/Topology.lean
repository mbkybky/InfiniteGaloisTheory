/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.Profinite.Basic

universe u v

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

namespace Homeomorph

protected lemma TotallyDisconnectedSpace {A : Type u} [TopologicalSpace A]
  {B : Type v} [TopologicalSpace B] (e : Homeomorph A B) [tdc : TotallyDisconnectedSpace A] :
  TotallyDisconnectedSpace B :=
  (totallyDisconnectedSpace_iff B).mpr
    ((Homeomorph.range_coe e) ▸
      ((Embedding.isTotallyDisconnected_range (Homeomorph.embedding e)).mpr tdc))

end Homeomorph

def Pi.profinite {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)
