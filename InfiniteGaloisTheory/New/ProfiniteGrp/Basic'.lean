/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu, Wanyi He
-/

import InfiniteGaloisTheory.New.ProfiniteGrp.Defs'

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

/-- A topological group that has a ContinuousMulEquivProfinite to a profinite group is profinite -/
def ofContinuousMulEquivProfiniteGrp {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
    [Group H] [TopologicalGroup H] (e : ContinuousMulEquiv G H) : ProfiniteGrp.{v} :=
  letI : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  letI : TotallyDisconnectedSpace G := Profinite.instTotallyDisconnectedSpaceαTopologicalSpaceToTop
  letI : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

/-- The closed subgroup of a profinite group is profinite -/
def ofClosedSubgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : ProfiniteGrp :=
  letI : CompactSpace H := isCompact_iff_compactSpace.mp (IsClosed.isCompact hH)
  of H

end ProfiniteGrp
