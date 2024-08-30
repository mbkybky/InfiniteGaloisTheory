/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G] (H : Type v) [Group H] [TopologicalSpace H] [TopologicalGroup H]

structure ContinuousMulEquiv extends MulEquiv G H , Homeomorph G H

namespace Homeomorph

protected lemma TotallyDisconnectedSpace {A : Type u} [TopologicalSpace A] {B : Type v} [TopologicalSpace B] (e : Homeomorph A B) [tdc : TotallyDisconnectedSpace A] : TotallyDisconnectedSpace B :=
  (totallyDisconnectedSpace_iff B).mpr ((Homeomorph.range_coe e) ▸ ((Embedding.isTotallyDisconnected_range (Homeomorph.embedding e)).mpr tdc))

end Homeomorph
