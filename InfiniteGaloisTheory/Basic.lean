/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yongle Hu, Nailin Guan
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.KrullTopology
import InfiniteGaloisTheory.ProFinite.Basic

/-example (k K : Type) [Field k] [Field K] [Algebra k K] :
  {L : (IntermediateField k K) | FiniteDimensional k L} ⥤ FiniteGrp := _

example (k K : Type) [Field k] [Field K] [Algebra k K] : ProfiniteGrp :=
ProfiniteGroup.of (K ≃ₐ[k] K)-/
