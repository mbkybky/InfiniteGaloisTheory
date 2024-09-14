/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Yi Song, Xuchun Li, Youle Fang
-/
import Mathlib.Topology.Algebra.OpenSubgroup

namespace TopologicalGroup

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Define the largest symmetric (self inverse) subset of a set -/
def symmCore (V : Set G) : Set G := V ∩ V⁻¹

lemma symmCore_spec (V : Set G) : (symmCore V) = (symmCore V)⁻¹ := by
  ext
  simp only [symmCore, Set.mem_inter_iff, Set.mem_inv, Set.inter_inv, inv_inv, and_comm]

lemma inter_symmCore_symm {α : Type*}
    (S : Set α) (V : α → Set G) : ⋂ a ∈ S, symmCore (V a) = (⋂ a ∈ S, symmCore (V a))⁻¹ := by
  ext x
  constructor <;>
  · intro h
    simp only [Set.iInter_coe_set, Set.mem_iInter, Set.iInter_inv, Set.mem_inv] at h ⊢
    intro s hs
    rw [symmCore_spec]
    simp only [Set.mem_inv, inv_inv, h s hs]

/-- Define the set of tuples `(x,y)` in a set `W` which `x * y` is in `W` too -/
private def mulClosurePairs (W : Set G) : Set (G × G) :=
  (fun (x, y) => x * y)⁻¹' W ∩ (W ×ˢ W)

private lemma mulClosurePairs_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) : IsOpen (mulClosurePairs W) := by
  let μ : G × G → G := fun (x, y) => x * y
  have μCont : Continuous μ := continuous_mul
  simp only [mulClosurePairs]
  apply IsOpen.inter (μCont.isOpen_preimage W <| WOpen) _
  apply IsOpen.prod <;> (exact WOpen)

private lemma mem_mulClosurePairs
    {W : Set G} (einW : 1 ∈ W) (w : W) : ((w : G), 1) ∈ mulClosurePairs W := by
  simp only [mulClosurePairs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, mul_one,
    Subtype.coe_prop, Subtype.coe_prop, einW, and_self]

/-- Define the first side of rectangle neighborhood of `(w,1)` in `mulClosurePairs` -/
private def nhdsSide' [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)

/-- Define the second side of rectangle neighborhood of `(w,1)` in `mulClosurePairs` -/
private def nhdsSide [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)

private lemma nhdsSide'_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    IsOpen (nhdsSide' WOpen einW w) :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).1

private lemma nhdsSide_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    IsOpen (nhdsSide WOpen einW w) :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.1

private lemma w_mem_nhdsSide' [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    w.1 ∈ (nhdsSide' WOpen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
      (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.1

private lemma one_mem_nhdsSide [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    1 ∈ (nhdsSide WOpen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
      (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.2.1

private lemma nhds_side_mul_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdsSide' WOpen einW w) ×ˢ (nhdsSide WOpen einW w) ⊆ mulClosurePairs W :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.2.2

/-- The symm core of `nhdsSide` -/
private def nhdsSideCore [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  symmCore (nhdsSide WOpen einW w)

private lemma nhdsSideCore_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : IsOpen (nhdsSideCore WOpen einW w)
    := by
  simp only [nhdsSideCore, symmCore]
  apply IsOpen.inter (nhdsSide_open WOpen einW w)
    (IsOpen.inv (nhdsSide_open WOpen einW w))

private lemma one_mem_nhdsSideCore [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    1 ∈ (nhdsSideCore WOpen einW w) := by
  simp only [nhdsSideCore, symmCore, Set.mem_inter_iff, Set.mem_inv, inv_one, and_self]
  exact (one_mem_nhdsSide WOpen einW w)

private lemma nhds_side_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdsSide' WOpen einW w) ⊆ W ∧ (nhdsSide WOpen einW w) ⊆ W:= by
  have mulClosurePairssubWp : mulClosurePairs W ⊆ (W ×ˢ W) := Set.inter_subset_right
  have := Set.Subset.trans (nhds_side_mul_sub WOpen einW w) mulClosurePairssubWp
  rw [Set.prod_subset_prod_iff] at this
  rcases this with h | e1 | e2
  · exact h
  · absurd e1
    exact ne_of_mem_of_not_mem' (w_mem_nhdsSide' WOpen einW w) fun a ↦ a
  · absurd e2
    exact ne_of_mem_of_not_mem' (one_mem_nhdsSide WOpen einW w) fun a ↦ a

private lemma nhdsSide'_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdsSide' WOpen einW w) ⊆ W := (nhds_side_sub WOpen einW w).1

private lemma nhdsSideCore_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdsSideCore WOpen einW w) ⊆ W := by
  simp only [nhdsSideCore, symmCore]
  exact Set.Subset.trans Set.inter_subset_left (nhds_side_sub WOpen einW w).2

private lemma nhdsSide'_cover [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ w : W, (nhdsSide' WOpen einW w) := by
  intro x xinW
  simp only [Set.iUnion_coe_set, Set.mem_iUnion]
  exact ⟨x, xinW, (w_mem_nhdsSide' WOpen einW ⟨x, xinW⟩)⟩

/-- The index of the finite subcover of the rectangle neighbors covering `(W,1)` -/
noncomputable def openSymmSubnhdsOfOneIndex [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Finset W :=
  Classical.choose (IsCompact.elim_finite_subcover (IsClosed.isCompact (IsClopen.isClosed WClopen))
    _ (fun (w : W) => (nhdsSide'_open WClopen.isOpen einW w)) (nhdsSide'_cover WClopen.isOpen einW))

lemma openSymmSubnhdsOfOneIndex_spec [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ i ∈ (openSymmSubnhdsOfOneIndex WClopen einW), nhdsSide' WClopen.isOpen einW i :=
  Classical.choose_spec (IsCompact.elim_finite_subcover (IsClosed.isCompact
  (IsClopen.isClosed WClopen)) _ (fun (w : W) => (nhdsSide'_open WClopen.isOpen einW w))
  (nhdsSide'_cover WClopen.isOpen einW))

/-- Define an open symmetric neighborhood of `1` such that it is contained in a given
  clopen neighborhood of `1` and the given neighborhood is closed under multiplying by
  an element in it. -/
def openSymmSubnhdsOfOne [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Set G :=
  ⋂ w ∈ (openSymmSubnhdsOfOneIndex WClopen einW) , nhdsSideCore WClopen.isOpen einW w

namespace openSymmSubnhdsOfOne

variable [TopologicalSpace G]  [TopologicalGroup G]

lemma isopen [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    IsOpen (openSymmSubnhdsOfOne WClopen einW) :=
  isOpen_biInter_finset (fun w _ => nhdsSideCore_open WClopen.isOpen einW w)

lemma symm [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    (openSymmSubnhdsOfOne WClopen einW) = (openSymmSubnhdsOfOne WClopen einW)⁻¹ := by
  simp only [openSymmSubnhdsOfOne, nhdsSideCore]
  apply inter_symmCore_symm

lemma one_mem [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    1 ∈ (openSymmSubnhdsOfOne WClopen einW) := by
  simp only [openSymmSubnhdsOfOne, Set.mem_iInter]
  exact fun w _ => one_mem_nhdsSideCore WClopen.isOpen einW w

lemma mul_sub [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W * (openSymmSubnhdsOfOne WClopen einW) ⊆ W := by
  intro a ainmul
  rcases ainmul with ⟨x,xinW,y,yinInter,xmuly⟩
  have fincover := openSymmSubnhdsOfOneIndex_spec WClopen einW
  have := fincover xinW
  simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at this
  rcases this with ⟨w,winfin,xinU⟩
  simp only [openSymmSubnhdsOfOne, Set.iUnion_coe_set, Set.iInter_coe_set, Set.mem_iInter
    ] at yinInter
  have yinV := Set.mem_of_mem_inter_left (yinInter w w.2 winfin)
  have := Set.mem_of_mem_inter_left <|
    nhds_side_mul_sub WClopen.isOpen einW w <| Set.mk_mem_prod xinU yinV
  simpa only [Set.mem_preimage, xmuly] using this

lemma sub [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    (openSymmSubnhdsOfOne WClopen einW) ⊆ W := by
  apply Set.Subset.trans _ (mul_sub WClopen einW)
  exact Set.subset_mul_right (openSymmSubnhdsOfOne WClopen einW) einW

end openSymmSubnhdsOfOne

end TopologicalGroup

section

open scoped Pointwise

open TopologicalGroup

private lemma iUnion_pow {G : Type*} [Group G] {V : Set G} (h : 1 ∈ V) :
    {x : G | ∃ n : ℕ, x ∈ V ^ n} = ⋃ n ≥ 1 , V ^ n := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨n,xin⟩
    cases' n with p
    · rw [pow_zero, Set.mem_one] at xin
      use 1
      simp_rw [ge_iff_le, le_refl, pow_one, Set.iUnion_true, xin]
      exact h
    · use (p + 1)
      simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true, xin]
  · intro h
    simp_rw [Set.mem_iUnion, exists_prop', nonempty_prop] at h
    rcases h with ⟨n,_,xin⟩
    use n

namespace TopologicalGroup

/-- Define an open symmetric neighborhood of `1` that is contained in a given
  clopen neighborhood of `1` -/
def OpenSubgroupSubnhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : OpenSubgroup G where
  carrier := {x : G | ∃ n : ℕ, x ∈ (openSymmSubnhdsOfOne WClopen einW) ^ n}
  mul_mem':= by
    rintro a b ⟨na, hna⟩ ⟨nb, hnb⟩
    simp only [Set.mem_setOf_eq] at *
    use na + nb
    rw [pow_add]
    exact Set.mul_mem_mul hna hnb
  one_mem':= by
    simp only [Set.mem_setOf_eq]
    use 1
    rw [pow_one]
    exact openSymmSubnhdsOfOne.one_mem WClopen einW
  inv_mem':= by
    simp only [Set.mem_setOf_eq, forall_exists_index] at *
    intro x m hm
    use m
    have : ∀ n : ℕ, ∀ x ∈ (openSymmSubnhdsOfOne WClopen einW) ^ n,
      x⁻¹ ∈ (openSymmSubnhdsOfOne WClopen einW) ^ n := by
      intro n
      induction' n with k hk
      · rw [pow_zero]
        intro x hx
        rw [hx]
        exact Set.mem_one.mpr inv_one
      · intro x hx
        rw [add_comm]
        rw [pow_add, pow_one] at *
        rcases hx with ⟨a, ha, b, hb, hyp⟩
        dsimp at hyp
        rw [← hyp, DivisionMonoid.mul_inv_rev a b]
        apply Set.mul_mem_mul _ (hk a ha)
        rw [openSymmSubnhdsOfOne.symm WClopen einW]
        exact Set.inv_mem_inv.mpr hb
    exact this m x hm
  isOpen' := by
    set V := (openSymmSubnhdsOfOne WClopen einW)
    let VOpen := openSymmSubnhdsOfOne.isopen WClopen einW
    let einV := openSymmSubnhdsOfOne.one_mem WClopen einW
    show IsOpen {x : G | ∃ n : ℕ, x ∈ V ^ n}
    rw [iUnion_pow einV]
    apply isOpen_iUnion
    intro n
    induction' n with n ih
    · simp_rw [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, pow_zero,
        Set.iUnion_of_empty, isOpen_empty]
    · cases' n
      · simp_rw [zero_add, ge_iff_le, le_refl, pow_one, Set.iUnion_true, VOpen]
      · simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, Set.iUnion_true] at ih ⊢
        rw [pow_succ]
        exact IsOpen.mul_left VOpen

theorem openSubgroupSubnhdsOfOne_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ((OpenSubgroupSubnhdsOfOne WClopen einW) : Set G) ⊆ W := by
  let V := (openSymmSubnhdsOfOne WClopen einW)
  let einV := openSymmSubnhdsOfOne.one_mem WClopen einW
  let mulVsubW := openSymmSubnhdsOfOne.mul_sub WClopen einW
  show {x : G | ∃ n : ℕ, x ∈ V ^ n} ⊆ W
  simp_rw [iUnion_pow einV, Set.iUnion_subset_iff]
  intro n nge
  have mulVpow: W * V ^ n ⊆ W := by
    induction' n with n ih
    · contradiction
    · cases' n with n
      · rw [zero_add, pow_one]
        exact mulVsubW
      · simp_rw [ge_iff_le, le_add_iff_nonneg_left, zero_le, true_implies] at ih
        rw [pow_succ, ← mul_assoc]
        exact le_trans (Set.mul_subset_mul_right ih) mulVsubW
  apply le_trans _ mulVpow
  intro x xin
  rw [Set.mem_mul]
  use 1, einW, x, xin
  rw [one_mul]

end TopologicalGroup

end
