/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/Overlap.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Logic.Relation
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-! # Overlap components of a finite family of finite sets

This file develops the connected components of a finite family `s : Finset (Finset α)`
of finite sets under the *overlap* relation: two sets overlap when they intersect.
This is the combinatorial backbone of the Kotecký–Preiss cluster expansion, where a
cluster decomposes uniquely into overlap-connected components after removal of a pivot.

## Main definitions

* `PolymerKP.Overlaps`: two finite sets overlap when they share an element.
* `PolymerKP.OverlapStep`: one step of overlap connectivity inside a family.
* `PolymerKP.OverlapReach`: overlap-reachability (reflexive-transitive closure).
* `PolymerKP.OverlapConn`: a family is overlap-connected.
* `PolymerKP.overlapComponentOf`: the overlap component of a member.
* `PolymerKP.overlapComponents`: the set of overlap components of a family.

## Main results

* `PolymerKP.sup_overlapComponents`: the components cover the family.
* `PolymerKP.overlapComponents_pairwiseDisjoint`: distinct components are disjoint.
* `PolymerKP.disjoint_sup_of_ne_overlapComponents`: supports of distinct components
  are disjoint.
* `PolymerKP.overlapComponents_unique`: the decomposition into nonempty,
  overlap-connected, support-disjoint subfamilies is unique.
* `PolymerKP.exists_overlaps_of_component_erase`: after erasing a member `B₀` from
  an overlap-connected family, every component of the remainder contains a set
  overlapping `B₀`.
-/

open scoped BigOperators

namespace PolymerKP

variable {α : Type*} [DecidableEq α]

/-- Two finite sets overlap when they share an element. -/
def Overlaps (A B : Finset α) : Prop := (A ∩ B).Nonempty

/-- One step of overlap connectivity inside the family `s`. -/
def OverlapStep (s : Finset (Finset α)) (A B : Finset α) : Prop :=
  A ∈ s ∧ B ∈ s ∧ Overlaps A B

/-- Overlap-reachability within the family `s`. -/
def OverlapReach (s : Finset (Finset α)) (A B : Finset α) : Prop :=
  Relation.ReflTransGen (OverlapStep s) A B

/-- The family `s` is overlap-connected (∅ and singleton families count as
connected). -/
def OverlapConn (s : Finset (Finset α)) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, OverlapReach s A B

open Classical in
/-- The overlap component of `A` within the family `s`. -/
noncomputable def overlapComponentOf (s : Finset (Finset α)) (A : Finset α) :
    Finset (Finset α) :=
  s.filter (OverlapReach s A)

open Classical in
/-- The set of overlap components of the family `s`. -/
noncomputable def overlapComponents (s : Finset (Finset α)) :
    Finset (Finset (Finset α)) :=
  s.image (overlapComponentOf s)

/-- Overlapping is a symmetric relation. -/
theorem Overlaps.symm {A B : Finset α} (h : Overlaps A B) : Overlaps B A := by
  unfold Overlaps at h ⊢
  rwa [Finset.inter_comm]

/-- One-step overlap connectivity is a symmetric relation. -/
theorem overlapStep_symmetric (s : Finset (Finset α)) : Symmetric (OverlapStep s) :=
  fun _A _B h => ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Overlap-reachability is a symmetric relation. -/
theorem OverlapReach.symm {s : Finset (Finset α)} {A B : Finset α}
    (h : OverlapReach s A B) : OverlapReach s B A :=
  Relation.ReflTransGen.symmetric (overlapStep_symmetric s) h

/-- Overlap-reachability is a transitive relation. -/
theorem OverlapReach.trans {s : Finset (Finset α)} {A B C : Finset α}
    (hAB : OverlapReach s A B) (hBC : OverlapReach s B C) : OverlapReach s A C :=
  Relation.ReflTransGen.trans hAB hBC

/-- Overlap-reachability is monotone in the ambient family. -/
theorem OverlapReach.mono {s t : Finset (Finset α)} {A B : Finset α} (hst : s ⊆ t)
    (h : OverlapReach s A B) : OverlapReach t A B :=
  Relation.ReflTransGen.mono (fun _X _Y hXY => ⟨hst hXY.1, hst hXY.2.1, hXY.2.2⟩) h

/-- Every set reached from a member of `s` is itself a member of `s`. -/
theorem OverlapReach.mem_right {s : Finset (Finset α)} {A B : Finset α}
    (h : OverlapReach s A B) (hA : A ∈ s) : B ∈ s := by
  induction h with
  | refl => exact hA
  | tail _hxb hstep _ih => exact hstep.2.1

/-- Membership in the overlap component of `A`. -/
theorem mem_overlapComponentOf {s : Finset (Finset α)} {A B : Finset α} :
    B ∈ overlapComponentOf s A ↔ B ∈ s ∧ OverlapReach s A B := by
  simp only [overlapComponentOf, Finset.mem_filter]

/-- A member of `s` belongs to its own overlap component. -/
theorem self_mem_overlapComponentOf {s : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ s) : A ∈ overlapComponentOf s A :=
  mem_overlapComponentOf.mpr ⟨hA, Relation.ReflTransGen.refl⟩

/-- Overlap components are subfamilies of `s`. -/
theorem overlapComponentOf_subset {s : Finset (Finset α)} {A : Finset α} :
    overlapComponentOf s A ⊆ s :=
  fun _B hB => (mem_overlapComponentOf.mp hB).1

/-- Overlap components that share a member coincide. -/
theorem overlapComponentOf_eq_of_mem {s : Finset (Finset α)} {A B : Finset α}
    (hB : B ∈ overlapComponentOf s A) :
    overlapComponentOf s B = overlapComponentOf s A := by
  obtain ⟨_hBs, hAB⟩ := mem_overlapComponentOf.mp hB
  ext C
  simp only [mem_overlapComponentOf]
  exact ⟨fun ⟨hCs, hBC⟩ => ⟨hCs, hAB.trans hBC⟩,
    fun ⟨hCs, hAC⟩ => ⟨hCs, hAB.symm.trans hAC⟩⟩

/-- A reachability chain within `s` starting at `A` can be realised entirely inside
the overlap component of `A`: every point of the chain lies in the component and
every step of the chain is a step within the component. -/
private theorem overlapReach_componentOf_of_overlapReach {s : Finset (Finset α)}
    {A X : Finset α} (h : OverlapReach s A X) :
    OverlapReach (overlapComponentOf s A) A X := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail W Z hxb hstep ih =>
    have hW : W ∈ overlapComponentOf s A :=
      mem_overlapComponentOf.mpr ⟨hstep.1, hxb⟩
    have hZ : Z ∈ overlapComponentOf s A :=
      mem_overlapComponentOf.mpr ⟨hstep.2.1, Relation.ReflTransGen.tail hxb hstep⟩
    exact Relation.ReflTransGen.tail ih ⟨hW, hZ, hstep.2.2⟩

/-- Reachability between two members of an overlap component can be realised
inside the component. -/
theorem overlapReach_within_component {s : Finset (Finset α)} {A : Finset α}
    {B C : Finset α} (hB : B ∈ overlapComponentOf s A)
    (hC : C ∈ overlapComponentOf s A) :
    OverlapReach (overlapComponentOf s A) B C := by
  obtain ⟨_hBs, hAB⟩ := mem_overlapComponentOf.mp hB
  obtain ⟨_hCs, hAC⟩ := mem_overlapComponentOf.mp hC
  exact (overlapReach_componentOf_of_overlapReach hAB).symm.trans
    (overlapReach_componentOf_of_overlapReach hAC)

/-- Every overlap component is overlap-connected. -/
theorem overlapConn_overlapComponentOf (s : Finset (Finset α)) (A : Finset α) :
    OverlapConn (overlapComponentOf s A) :=
  fun _B hB _C hC => overlapReach_within_component hB hC

/-- Every overlap component of a family is a nonempty family. -/
theorem overlapComponents_nonempty {s : Finset (Finset α)}
    {c : Finset (Finset α)} (hc : c ∈ overlapComponents s) : c.Nonempty := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨A, self_mem_overlapComponentOf hA⟩

/-- Every overlap component of a family is a subfamily. -/
theorem overlapComponents_subset {s : Finset (Finset α)}
    {c : Finset (Finset α)} (hc : c ∈ overlapComponents s) : c ⊆ s := by
  obtain ⟨A, _hA, rfl⟩ := Finset.mem_image.mp hc
  exact overlapComponentOf_subset

/-- Every overlap component of a family is overlap-connected. -/
theorem overlapConn_of_mem_overlapComponents {s : Finset (Finset α)}
    {c : Finset (Finset α)} (hc : c ∈ overlapComponents s) : OverlapConn c := by
  obtain ⟨A, _hA, rfl⟩ := Finset.mem_image.mp hc
  exact overlapConn_overlapComponentOf s A

/-- The overlap components of `s` cover `s`. -/
theorem sup_overlapComponents (s : Finset (Finset α)) :
    (overlapComponents s).sup id = s := by
  apply Finset.Subset.antisymm
  · intro A hA
    obtain ⟨c, hc, hAc⟩ := Finset.mem_sup.mp hA
    exact overlapComponents_subset hc hAc
  · intro A hA
    exact Finset.mem_sup.mpr ⟨overlapComponentOf s A,
      Finset.mem_image_of_mem _ hA, self_mem_overlapComponentOf hA⟩

/-- Distinct overlap components are disjoint families. -/
theorem overlapComponents_pairwiseDisjoint (s : Finset (Finset α)) :
    ((overlapComponents s : Set (Finset (Finset α)))).Pairwise
      fun c c' => Disjoint c c' := by
  intro c hc c' hc' hne
  show Disjoint c c'
  rw [Finset.disjoint_left]
  intro B hBc hBc'
  obtain ⟨A, _hA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
  obtain ⟨A', _hA', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc')
  exact hne ((overlapComponentOf_eq_of_mem hBc).symm.trans
    (overlapComponentOf_eq_of_mem hBc'))

/-- Supports (unions) of distinct overlap components are disjoint. -/
theorem disjoint_sup_of_ne_overlapComponents {s : Finset (Finset α)}
    {c c' : Finset (Finset α)} (hc : c ∈ overlapComponents s)
    (hc' : c' ∈ overlapComponents s) (hne : c ≠ c') :
    Disjoint (c.sup id) (c'.sup id) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨A, hAc, hxA⟩ := Finset.mem_sup.mp hx
  obtain ⟨B, hBc', hxB⟩ := Finset.mem_sup.mp hx'
  obtain ⟨A₀, _hA₀, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨B₀, _hB₀, rfl⟩ := Finset.mem_image.mp hc'
  have hAs : A ∈ s := overlapComponentOf_subset hAc
  have hBs : B ∈ s := overlapComponentOf_subset hBc'
  have hstep : OverlapStep s A B :=
    ⟨hAs, hBs, ⟨x, Finset.mem_inter.mpr ⟨hxA, hxB⟩⟩⟩
  have hBcomp : B ∈ overlapComponentOf s A₀ :=
    mem_overlapComponentOf.mpr
      ⟨hBs, Relation.ReflTransGen.tail (mem_overlapComponentOf.mp hAc).2 hstep⟩
  exact hne ((overlapComponentOf_eq_of_mem hBcomp).symm.trans
    (overlapComponentOf_eq_of_mem hBc'))

set_option linter.unusedVariables false in
/-- **Uniqueness of the overlap decomposition.** Any family `T` of nonempty,
overlap-connected subfamilies with pairwise disjoint supports covering `s` is
exactly the family of overlap components of `s`. (The hypothesis `hmemne` is kept
for interface stability with the Kotecký–Preiss development; the proof only needs
disjointness of the supports.) -/
theorem overlapComponents_unique {s : Finset (Finset α)}
    {T : Finset (Finset (Finset α))}
    (hne : ∀ c ∈ T, c.Nonempty)
    (hconn : ∀ c ∈ T, OverlapConn c)
    (hmemne : ∀ c ∈ T, ∀ A ∈ c, A.Nonempty)
    (hdisj : (T : Set (Finset (Finset α))).Pairwise
      fun c c' => Disjoint (c.sup id) (c'.sup id))
    (hcover : T.sup id = s) :
    T = overlapComponents s := by
  -- every member of `T` is a subfamily of `s`
  have hsub : ∀ c ∈ T, c ⊆ s := by
    intro c hc
    have h := Finset.le_sup (f := id) hc
    rw [hcover] at h
    exact Finset.le_iff_subset.mp h
  -- key identity: each `c ∈ T` is the overlap component of any of its members
  have hkey : ∀ c ∈ T, ∀ A ∈ c, c = overlapComponentOf s A := by
    intro c hc A hA
    apply Finset.Subset.antisymm
    · -- `c ⊆ overlapComponentOf s A`: reachability within `c` maps into `s`
      intro B hB
      exact mem_overlapComponentOf.mpr
        ⟨hsub c hc hB, OverlapReach.mono (hsub c hc) (hconn c hc A hA B hB)⟩
    · -- `overlapComponentOf s A ⊆ c`: membership in `c` is closed under
      -- `OverlapStep s`, by support-disjointness of the pieces of `T`
      intro B hB
      have hAB : OverlapReach s A B := (mem_overlapComponentOf.mp hB).2
      clear hB
      induction hAB with
      | refl => exact hA
      | @tail W Z _hxb hstep ih =>
        have hZsup : Z ∈ T.sup id := by rw [hcover]; exact hstep.2.1
        obtain ⟨c', hc', hZc'⟩ := Finset.mem_sup.mp hZsup
        obtain ⟨x, hx⟩ := hstep.2.2
        have hcc' : c = c' := by
          by_contra hne'
          exact Finset.disjoint_left.mp
            (hdisj (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hne')
            (Finset.mem_sup.mpr ⟨W, ih, (Finset.mem_inter.mp hx).1⟩)
            (Finset.mem_sup.mpr ⟨Z, hZc', (Finset.mem_inter.mp hx).2⟩)
        rw [hcc']
        exact hZc'
  apply Finset.Subset.antisymm
  · -- `T ⊆ overlapComponents s`
    intro c hc
    obtain ⟨A, hA⟩ := hne c hc
    rw [hkey c hc A hA]
    exact Finset.mem_image_of_mem _ (hsub c hc hA)
  · -- `overlapComponents s ⊆ T`
    intro c hc
    obtain ⟨A, hAs, rfl⟩ := Finset.mem_image.mp hc
    have hAsup : A ∈ T.sup id := by rw [hcover]; exact hAs
    obtain ⟨c', hc', hAc'⟩ := Finset.mem_sup.mp hAsup
    rw [← hkey c' hc' A hAc']
    exact hc'

/-- **Pivot removal.** If `s` is overlap-connected and `B₀ ∈ s`, then every overlap
component of `s.erase B₀` contains a set overlapping `B₀`. -/
theorem exists_overlaps_of_component_erase {s : Finset (Finset α)}
    (hconn : OverlapConn s) {B₀ : Finset α} (hB₀ : B₀ ∈ s)
    {c : Finset (Finset α)} (hc : c ∈ overlapComponents (s.erase B₀)) :
    ∃ A ∈ c, Overlaps A B₀ := by
  obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hc
  have hA₀s : A₀ ∈ s := Finset.mem_of_mem_erase hA₀
  have hA₀ne : A₀ ≠ B₀ := Finset.ne_of_mem_erase hA₀
  have hreach : OverlapReach s A₀ B₀ := hconn A₀ hA₀s B₀ hB₀
  -- strengthened claim: any chain in `s` from `A₀` either avoids `B₀` and restricts
  -- to `s.erase B₀`, or produces a set reachable in `s.erase B₀` overlapping `B₀`
  have key : ∀ X, OverlapReach s A₀ X →
      (OverlapReach (s.erase B₀) A₀ X ∧ X ≠ B₀) ∨
        ∃ Y, OverlapReach (s.erase B₀) A₀ Y ∧ Overlaps Y B₀ := by
    intro X hX
    induction hX with
    | refl => exact Or.inl ⟨Relation.ReflTransGen.refl, hA₀ne⟩
    | @tail W Z _hxb hstep ih =>
      rcases ih with ⟨hreach', hWne⟩ | hright
      · by_cases hZ : Z = B₀
        · subst hZ
          exact Or.inr ⟨W, hreach', hstep.2.2⟩
        · refine Or.inl ⟨Relation.ReflTransGen.tail hreach' ?_, hZ⟩
          exact ⟨Finset.mem_erase.mpr ⟨hWne, hstep.1⟩,
            Finset.mem_erase.mpr ⟨hZ, hstep.2.1⟩, hstep.2.2⟩
      · exact Or.inr hright
  rcases key B₀ hreach with ⟨_, hne'⟩ | ⟨Y, hYreach, hYov⟩
  · exact absurd rfl hne'
  · exact ⟨Y, mem_overlapComponentOf.mpr
      ⟨OverlapReach.mem_right hYreach hA₀, hYreach⟩, hYov⟩

/-- An overlap-connected family is its own overlap component at any of its
members. -/
theorem overlapComponentOf_congr_of_conn {s : Finset (Finset α)}
    (h : OverlapConn s) {A : Finset α} (hA : A ∈ s) :
    overlapComponentOf s A = s := by
  apply Finset.Subset.antisymm overlapComponentOf_subset
  intro B hB
  exact mem_overlapComponentOf.mpr ⟨hB, h A hA B hB⟩

/-- A nonempty overlap-connected family has itself as its only overlap component. -/
theorem overlapComponents_eq_singleton_of_conn {s : Finset (Finset α)}
    (h : OverlapConn s) (hs : s.Nonempty) : overlapComponents s = {s} := by
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_singleton]
    exact overlapComponentOf_congr_of_conn h hA
  · intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    obtain ⟨A, hA⟩ := hs
    exact Finset.mem_image.mpr ⟨A, hA, overlapComponentOf_congr_of_conn h hA⟩

/-- The empty family has no overlap components. -/
theorem overlapComponents_empty :
    overlapComponents (∅ : Finset (Finset α)) = ∅ := by
  simp [overlapComponents]

/-- A member outside the component of `A₀` does not meet the component's
support. -/
theorem notMem_sup_component_of_notMem {s : Finset (Finset α)}
    {A₀ A : Finset α} (hA : A ∈ s)
    (hAnot : A ∉ overlapComponentOf s A₀) :
    ∀ x ∈ A, x ∉ (overlapComponentOf s A₀).sup id := by
  intro x hxA hxsup
  rw [Finset.mem_sup] at hxsup
  obtain ⟨B, hB, hxB⟩ := hxsup
  rcases mem_overlapComponentOf.1 hB with ⟨hBs, hreach⟩
  refine hAnot (mem_overlapComponentOf.2 ⟨hA, ?_⟩)
  exact hreach.tail ⟨hBs, hA, ⟨x, Finset.mem_inter.2 ⟨hxB, hxA⟩⟩⟩

/-- Removing a whole component removes exactly that component from the
component decomposition. -/
theorem overlapComponents_sdiff_component {s : Finset (Finset α)}
    (hmemne : ∀ A ∈ s, A.Nonempty) {A₀ : Finset α} (hA₀ : A₀ ∈ s) :
    overlapComponents (s \ overlapComponentOf s A₀)
      = (overlapComponents s).erase (overlapComponentOf s A₀) := by
  classical
  set c₀ := overlapComponentOf s A₀ with hc₀
  have hc₀mem : c₀ ∈ overlapComponents s :=
    Finset.mem_image_of_mem _ hA₀
  refine (overlapComponents_unique ?_ ?_ ?_ ?_ ?_).symm
  · intro c hc
    exact overlapComponents_nonempty (Finset.mem_of_mem_erase hc)
  · intro c hc
    exact overlapConn_of_mem_overlapComponents (Finset.mem_of_mem_erase hc)
  · intro c hc A hA
    exact hmemne A (overlapComponents_subset (Finset.mem_of_mem_erase hc) hA)
  · intro c hc c' hc' hne
    exact disjoint_sup_of_ne_overlapComponents
      (Finset.mem_of_mem_erase hc) (Finset.mem_of_mem_erase hc') hne
  · apply Finset.Subset.antisymm
    · intro A hA
      rw [Finset.mem_sup] at hA
      obtain ⟨c, hc, hAc⟩ := hA
      have hcmem := Finset.mem_of_mem_erase hc
      have hcne := Finset.ne_of_mem_erase hc
      refine Finset.mem_sdiff.2
        ⟨overlapComponents_subset hcmem hAc, fun hAc₀ => ?_⟩
      exact Finset.disjoint_left.1
        (overlapComponents_pairwiseDisjoint s hcmem hc₀mem hcne) hAc hAc₀
    · intro A hA
      rcases Finset.mem_sdiff.1 hA with ⟨hAs, hAc₀⟩
      have hAmem : A ∈ overlapComponentOf s A := self_mem_overlapComponentOf hAs
      have hAcomp : overlapComponentOf s A ∈ overlapComponents s :=
        Finset.mem_image_of_mem _ hAs
      have hne : overlapComponentOf s A ≠ c₀ := by
        intro h
        exact hAc₀ (h ▸ hAmem)
      rw [Finset.mem_sup]
      exact ⟨overlapComponentOf s A,
        Finset.mem_erase.2 ⟨hne, hAcomp⟩, hAmem⟩

end PolymerKP
