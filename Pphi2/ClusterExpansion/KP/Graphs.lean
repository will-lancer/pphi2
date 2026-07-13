/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/Graphs.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Graphs as edge Finsets, connected-graph sums, and the exponential formula

Combinatorial backbone of the Kotecký–Preiss cluster expansion (FV Chapter 5).

A "graph on a finite vertex set `V : Finset ι`" is an edge set
`E : Finset (Sym2 ι)` with `E ⊆ pairsOn V` (non-diagonal unordered pairs inside
`V`).  We develop:

* `Reach E` — reachability through the edges of `E` (`Relation.ReflTransGen`);
* `ConnOn V E` — `E` is a connected spanning edge set on `V` (by convention the
  empty vertex set and singletons are connected);
* `graphSum V z` / `connSum V z` — sums over all (resp. all connected spanning)
  edge sets on `V` of the product of edge weights `z`;
* the component decomposition of `graphSum` (FV (5.7)), the exponential formula
  `graphSum V z = ∑ partitions P, ∏ blocks W, connSum W z`, and the star
  decomposition of `connSum (insert v₀ V)` used in the Kotecký–Preiss induction
  (FV Theorem 5.4).

Everything is classical; the sums are over `Finset`-filtered index sets with
`Classical` decidability, which is harmless because all uses are inside
noncomputable analytic developments.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace PolymerKP

variable {ι : Type*} [DecidableEq ι]

/-! ### Edges on a finite vertex set -/

/-- The non-diagonal unordered pairs with both endpoints in `V`: the edge set of
the complete graph on `V`. -/
def pairsOn (V : Finset ι) : Finset (Sym2 ι) :=
  V.sym2.filter fun e => ¬ e.IsDiag

theorem mk_mem_pairsOn_iff {V : Finset ι} {a b : ι} :
    s(a, b) ∈ pairsOn V ↔ (a ∈ V ∧ b ∈ V) ∧ a ≠ b := by
  simp [pairsOn, Finset.mk_mem_sym2_iff]

theorem pairsOn_mono {V W : Finset ι} (h : V ⊆ W) : pairsOn V ⊆ pairsOn W := by
  intro e he
  induction e with
  | _ a b =>
      rw [mk_mem_pairsOn_iff] at he ⊢
      exact ⟨⟨h he.1.1, h he.1.2⟩, he.2⟩

theorem disjoint_pairsOn_of_disjoint {A B : Finset ι} (h : Disjoint A B) :
    Disjoint (pairsOn A) (pairsOn B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  induction e with
  | _ a b =>
      rw [mk_mem_pairsOn_iff] at heA heB
      exact (Finset.disjoint_left.1 h) heA.1.1 heB.1.1

theorem pairsOn_empty : pairsOn (∅ : Finset ι) = ∅ := by
  ext e
  induction e with
  | _ a b => simp [mk_mem_pairsOn_iff]

theorem pairsOn_singleton (v : ι) : pairsOn ({v} : Finset ι) = ∅ := by
  ext e
  induction e with
  | _ a b =>
      simp only [mk_mem_pairsOn_iff, Finset.mem_singleton, Finset.notMem_empty,
        iff_false]
      rintro ⟨⟨rfl, rfl⟩, hne⟩
      exact hne rfl

/-! ### Adjacency and reachability through an edge set -/

/-- One-step adjacency through the edge set `E`. -/
def Adj (E : Finset (Sym2 ι)) (u v : ι) : Prop :=
  u ≠ v ∧ s(u, v) ∈ E

theorem Adj.symm {E : Finset (Sym2 ι)} {u v : ι} (h : Adj E u v) : Adj E v u :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

theorem adj_symmetric (E : Finset (Sym2 ι)) : Symmetric (Adj E) :=
  fun _ _ h => h.symm

theorem Adj.mono {E F : Finset (Sym2 ι)} (hEF : E ⊆ F) {u v : ι}
    (h : Adj E u v) : Adj F u v :=
  ⟨h.1, hEF h.2⟩

theorem Adj.mem_left_of_subset_pairsOn {E : Finset (Sym2 ι)} {V : Finset ι}
    (hE : E ⊆ pairsOn V) {u v : ι} (h : Adj E u v) : u ∈ V := by
  have := hE h.2
  rw [mk_mem_pairsOn_iff] at this
  exact this.1.1

theorem Adj.mem_right_of_subset_pairsOn {E : Finset (Sym2 ι)} {V : Finset ι}
    (hE : E ⊆ pairsOn V) {u v : ι} (h : Adj E u v) : v ∈ V :=
  h.symm.mem_left_of_subset_pairsOn hE

/-- Reachability through the edge set `E`. -/
def Reach (E : Finset (Sym2 ι)) : ι → ι → Prop :=
  Relation.ReflTransGen (Adj E)

@[refl]
theorem Reach.refl {E : Finset (Sym2 ι)} (v : ι) : Reach E v v :=
  Relation.ReflTransGen.refl

theorem Reach.symm {E : Finset (Sym2 ι)} {u v : ι} (h : Reach E u v) :
    Reach E v u :=
  Relation.ReflTransGen.symmetric (adj_symmetric E) h

theorem Reach.trans {E : Finset (Sym2 ι)} {u v w : ι}
    (huv : Reach E u v) (hvw : Reach E v w) : Reach E u w :=
  Relation.ReflTransGen.trans huv hvw

theorem Reach.mono {E F : Finset (Sym2 ι)} (hEF : E ⊆ F) {u v : ι}
    (h : Reach E u v) : Reach F u v :=
  Relation.ReflTransGen.mono (fun _ _ hadj => hadj.mono hEF) h

theorem Adj.reach {E : Finset (Sym2 ι)} {u v : ι} (h : Adj E u v) :
    Reach E u v :=
  Relation.ReflTransGen.single h

/-- Reachability stays inside any set of vertices that is closed under
one-step adjacency. -/
theorem Reach.mem_of_closed {E : Finset (Sym2 ι)} {p : ι → Prop}
    (hp : ∀ ⦃u v : ι⦄, Adj E u v → p u → p v)
    {x y : ι} (h : Reach E x y) (hx : p x) : p y := by
  induction h with
  | refl => exact hx
  | tail _ hadj ih => exact hp hadj ih

/-- A reachability path starting in a vertex set `A` that is closed under
one-step adjacency can be realised using only the edges lying inside `A`. -/
theorem Reach.filter_pairsOn {E : Finset (Sym2 ι)} {A : Finset ι}
    (hA : ∀ ⦃u v : ι⦄, Adj E u v → u ∈ A → v ∈ A)
    {x y : ι} (h : Reach E x y) (hx : x ∈ A) :
    Reach (E.filter fun e => e ∈ pairsOn A) x y := by
  classical
  induction h with
  | refl => exact Reach.refl x
  | @tail b c hxb hadj ih =>
      have hb : b ∈ A := Reach.mem_of_closed hA hxb hx
      have hc : c ∈ A := hA hadj hb
      refine Relation.ReflTransGen.tail ih ⟨hadj.1, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hadj.2, mk_mem_pairsOn_iff.2 ⟨⟨hb, hc⟩, hadj.1⟩⟩

/-! ### Connected spanning edge sets -/

/-- `E` is a connected spanning edge set on `V`: all edges lie inside `V`, and
any two vertices of `V` are joined through `E`.  By this convention `∅` is a
connected edge set on `∅` and on any singleton. -/
def ConnOn (V : Finset ι) (E : Finset (Sym2 ι)) : Prop :=
  E ⊆ pairsOn V ∧ ∀ u ∈ V, ∀ v ∈ V, Reach E u v

open Classical in
/-- All connected spanning edge sets on `V`. -/
noncomputable def connGraphsOn (V : Finset ι) : Finset (Finset (Sym2 ι)) :=
  (pairsOn V).powerset.filter fun E => ConnOn V E

theorem mem_connGraphsOn {V : Finset ι} {E : Finset (Sym2 ι)} :
    E ∈ connGraphsOn V ↔ ConnOn V E := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h.1, h⟩

theorem connGraphsOn_empty : connGraphsOn (∅ : Finset ι) = {∅} := by
  ext E
  rw [mem_connGraphsOn, Finset.mem_singleton]
  constructor
  · intro h
    have := h.1
    rw [pairsOn_empty, Finset.subset_empty] at this
    exact this
  · rintro rfl
    exact ⟨by rw [pairsOn_empty], fun u hu => absurd hu (Finset.notMem_empty u)⟩

theorem connGraphsOn_singleton (v : ι) : connGraphsOn ({v} : Finset ι) = {∅} := by
  ext E
  rw [mem_connGraphsOn, Finset.mem_singleton]
  constructor
  · intro h
    have := h.1
    rw [pairsOn_singleton, Finset.subset_empty] at this
    exact this
  · rintro rfl
    refine ⟨by rw [pairsOn_singleton], ?_⟩
    intro u hu w hw
    rw [Finset.mem_singleton] at hu hw
    subst hu; subst hw
    exact Reach.refl _

/-! ### Graph sums -/

/-- Sum over all spanning edge sets on `V` of the product of edge weights. -/
noncomputable def graphSum (V : Finset ι) (z : Sym2 ι → ℝ) : ℝ :=
  ∑ E ∈ (pairsOn V).powerset, ∏ e ∈ E, z e

/-- Sum over connected spanning edge sets on `V` of the product of edge
weights. -/
noncomputable def connSum (V : Finset ι) (z : Sym2 ι → ℝ) : ℝ :=
  ∑ E ∈ connGraphsOn V, ∏ e ∈ E, z e

theorem graphSum_empty (z : Sym2 ι → ℝ) : graphSum (∅ : Finset ι) z = 1 := by
  simp [graphSum, pairsOn_empty]

theorem connSum_empty (z : Sym2 ι → ℝ) : connSum (∅ : Finset ι) z = 1 := by
  simp [connSum, connGraphsOn_empty]

theorem connSum_singleton (v : ι) (z : Sym2 ι → ℝ) :
    connSum ({v} : Finset ι) z = 1 := by
  simp [connSum, connGraphsOn_singleton]

theorem graphSum_congr {V : Finset ι} {z z' : Sym2 ι → ℝ}
    (h : ∀ e ∈ pairsOn V, z e = z' e) : graphSum V z = graphSum V z' := by
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [Finset.mem_powerset] at hE
  exact Finset.prod_congr rfl fun e he => h e (hE he)

theorem connSum_congr {V : Finset ι} {z z' : Sym2 ι → ℝ}
    (h : ∀ e ∈ pairsOn V, z e = z' e) : connSum V z = connSum V z' := by
  refine Finset.sum_congr rfl fun E hE => ?_
  have hsub := (mem_connGraphsOn.1 hE).1
  exact Finset.prod_congr rfl fun e he => h e (hsub he)

/-! ### Components -/

open Classical in
/-- The connected component of `v₀` inside `V` under the edges `E`. -/
noncomputable def componentOf (E : Finset (Sym2 ι)) (V : Finset ι) (v₀ : ι) :
    Finset ι :=
  V.filter fun v => Reach E v₀ v

theorem mem_componentOf {E : Finset (Sym2 ι)} {V : Finset ι} {v₀ v : ι} :
    v ∈ componentOf E V v₀ ↔ v ∈ V ∧ Reach E v₀ v := by
  classical
  simp [componentOf]

theorem componentOf_subset {E : Finset (Sym2 ι)} {V : Finset ι} {v₀ : ι} :
    componentOf E V v₀ ⊆ V := by
  intro v hv
  exact (mem_componentOf.1 hv).1

theorem self_mem_componentOf {E : Finset (Sym2 ι)} {V : Finset ι} {v₀ : ι}
    (hv₀ : v₀ ∈ V) : v₀ ∈ componentOf E V v₀ :=
  mem_componentOf.2 ⟨hv₀, Reach.refl v₀⟩

/-- The component of `v₀` is closed under one-step adjacency, provided all
edges lie inside `V`. -/
theorem componentOf_closed {E : Finset (Sym2 ι)} {V : Finset ι} {v₀ : ι}
    (hE : E ⊆ pairsOn V) :
    ∀ ⦃u v : ι⦄, Adj E u v → u ∈ componentOf E V v₀ → v ∈ componentOf E V v₀ := by
  intro u v hadj hu
  rcases mem_componentOf.1 hu with ⟨_, hreach⟩
  exact mem_componentOf.2
    ⟨hadj.mem_right_of_subset_pairsOn hE, hreach.trans hadj.reach⟩

/-- Two components are equal as soon as they share a vertex. -/
theorem componentOf_eq_of_mem {E : Finset (Sym2 ι)} {V : Finset ι} {u v : ι}
    (hv : v ∈ componentOf E V u) :
    componentOf E V v = componentOf E V u := by
  rcases mem_componentOf.1 hv with ⟨_, huv⟩
  ext w
  rw [mem_componentOf, mem_componentOf]
  constructor
  · rintro ⟨hwV, hvw⟩
    exact ⟨hwV, huv.trans hvw⟩
  · rintro ⟨hwV, huw⟩
    exact ⟨hwV, huv.symm.trans huw⟩

/-! ### Unordered partitions of a finite vertex set -/

open Classical in
/-- All partitions of `V` into nonempty pairwise-disjoint blocks, encoded as the
`Finset` of blocks (the blocks, being distinct nonempty sets, determine the
partition). -/
noncomputable def partitionsOn (V : Finset ι) : Finset (Finset (Finset ι)) :=
  V.powerset.powerset.filter fun P =>
    (∀ W ∈ P, W.Nonempty) ∧
    ((P : Set (Finset ι)).Pairwise fun W W' => Disjoint W W') ∧
    P.sup id = V

theorem mem_partitionsOn {V : Finset ι} {P : Finset (Finset ι)} :
    P ∈ partitionsOn V ↔
      (∀ W ∈ P, W.Nonempty) ∧
      ((P : Set (Finset ι)).Pairwise fun W W' => Disjoint W W') ∧
      P.sup id = V := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    rw [Finset.mem_powerset]
    intro W hW
    rw [Finset.mem_powerset]
    have : W ≤ P.sup id := Finset.le_sup (f := id) hW
    rw [h.2.2] at this
    exact this

theorem block_subset_of_mem_partitionsOn {V : Finset ι} {P : Finset (Finset ι)}
    (hP : P ∈ partitionsOn V) {W : Finset ι} (hW : W ∈ P) : W ⊆ V := by
  have h := (mem_partitionsOn.1 hP).2.2
  have : W ≤ P.sup id := Finset.le_sup (f := id) hW
  rw [h] at this
  exact this

theorem partitionsOn_empty : partitionsOn (∅ : Finset ι) = {∅} := by
  ext P
  rw [mem_partitionsOn, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, _, hsup⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro W hW
    have hsub : W ⊆ (∅ : Finset ι) := by
      have : W ≤ P.sup id := Finset.le_sup (f := id) hW
      rw [hsup] at this
      exact this
    rcases hne W hW with ⟨x, hx⟩
    exact Finset.notMem_empty x (hsub hx)
  · rintro rfl
    exact ⟨fun W hW => absurd hW (Finset.notMem_empty W), by simp, by simp⟩

/-- The block of a partition containing a given vertex. -/
theorem exists_unique_block {V : Finset ι} {P : Finset (Finset ι)}
    (hP : P ∈ partitionsOn V) {v : ι} (hv : v ∈ V) :
    ∃! W, W ∈ P ∧ v ∈ W := by
  obtain ⟨_, hdisj, hsup⟩ := mem_partitionsOn.1 hP
  have : v ∈ P.sup id := hsup ▸ hv
  rw [Finset.mem_sup] at this
  obtain ⟨W, hW, hvW⟩ := this
  refine ⟨W, ⟨hW, hvW⟩, ?_⟩
  rintro W' ⟨hW', hvW'⟩
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj hW' hW hne) hvW' hvW

theorem erase_mem_partitionsOn_sdiff {V : Finset ι} {P : Finset (Finset ι)}
    (hP : P ∈ partitionsOn V) {W₀ : Finset ι} (hW₀ : W₀ ∈ P) :
    P.erase W₀ ∈ partitionsOn (V \ W₀) := by
  obtain ⟨hne, hdisj, hsup⟩ := mem_partitionsOn.1 hP
  refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
  · intro W hW
    exact hne W (Finset.mem_of_mem_erase hW)
  · intro W hW W' hW' hne'
    exact hdisj (Finset.mem_of_mem_erase hW) (Finset.mem_of_mem_erase hW') hne'
  · apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_sup] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      have hWP := Finset.mem_of_mem_erase hW
      have hWne := Finset.ne_of_mem_erase hW
      refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
      · have : W ≤ P.sup id := Finset.le_sup (f := id) hWP
        rw [hsup] at this
        exact this hxW
      · intro hxW₀
        exact Finset.disjoint_left.1 (hdisj hWP hW₀ hWne) hxW hxW₀
    · intro x hx
      rcases Finset.mem_sdiff.1 hx with ⟨hxV, hxW₀⟩
      obtain ⟨W, ⟨hW, hxW⟩, _⟩ := exists_unique_block hP hxV
      have hWne : W ≠ W₀ := fun h => hxW₀ (h ▸ hxW)
      rw [Finset.mem_sup]
      exact ⟨W, Finset.mem_erase.2 ⟨hWne, hW⟩, hxW⟩

theorem notMem_of_disjoint_partitionsOn {V' : Finset ι} {P : Finset (Finset ι)}
    (hP : P ∈ partitionsOn V') {W₀ : Finset ι} (hW₀ : W₀.Nonempty)
    (hdisj : Disjoint W₀ V') : W₀ ∉ P := by
  intro hmem
  rcases hW₀ with ⟨x, hx⟩
  have hsub := block_subset_of_mem_partitionsOn hP hmem
  exact Finset.disjoint_left.1 hdisj hx (hsub hx)

theorem insert_mem_partitionsOn {V' : Finset ι} {P : Finset (Finset ι)}
    (hP : P ∈ partitionsOn V') {W₀ : Finset ι} (hW₀ : W₀.Nonempty)
    (hdisj : Disjoint W₀ V') :
    insert W₀ P ∈ partitionsOn (W₀ ∪ V') := by
  obtain ⟨hne, hpdisj, hsup⟩ := mem_partitionsOn.1 hP
  refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
  · intro W hW
    rcases Finset.mem_insert.1 hW with rfl | hWP
    · exact hW₀
    · exact hne W hWP
  · intro W hW W' hW' hne'
    rcases Finset.mem_insert.1 hW with rfl | hWP <;>
      rcases Finset.mem_insert.1 hW' with rfl | hW'P
    · exact absurd rfl hne'
    · exact hdisj.mono_right (block_subset_of_mem_partitionsOn hP hW'P)
    · exact (hdisj.mono_right (block_subset_of_mem_partitionsOn hP hWP)).symm
    · exact hpdisj hWP hW'P hne'
  · rw [Finset.sup_insert, hsup]
    rfl

/-! ### The component split of the full graph sum -/

section ComponentSplit

variable {V : Finset ι} {v₀ : ι}

/-- Restricting the edges of `E` to the component of `v₀` yields a connected
spanning edge set on that component. -/
theorem filter_component_connOn {E : Finset (Sym2 ι)}
    (hE : E ⊆ pairsOn V) (hv₀ : v₀ ∈ V) :
    ConnOn (componentOf E V v₀)
      (E.filter fun e => e ∈ pairsOn (componentOf E V v₀)) := by
  classical
  constructor
  · intro e he
    exact (Finset.mem_filter.1 he).2
  · intro u hu v hv
    have hu' := mem_componentOf.1 hu
    have hv' := mem_componentOf.1 hv
    have h1 : Reach (E.filter fun e => e ∈ pairsOn (componentOf E V v₀)) v₀ u :=
      Reach.filter_pairsOn (componentOf_closed hE) hu'.2
        (self_mem_componentOf hv₀)
    have h2 : Reach (E.filter fun e => e ∈ pairsOn (componentOf E V v₀)) v₀ v :=
      Reach.filter_pairsOn (componentOf_closed hE) hv'.2
        (self_mem_componentOf hv₀)
    exact h1.symm.trans h2

/-- The edges of `E` outside the component of `v₀` lie in the complement. -/
theorem sdiff_filter_component_subset {E : Finset (Sym2 ι)}
    (hE : E ⊆ pairsOn V) :
    E \ (E.filter fun e => e ∈ pairsOn (componentOf E V v₀))
      ⊆ pairsOn (V \ componentOf E V v₀) := by
  classical
  intro e
  induction e with
  | _ a b =>
      intro hab
      rcases Finset.mem_sdiff.1 hab with ⟨haE, hnotF⟩
      have hnot : s(a, b) ∉ pairsOn (componentOf E V v₀) := fun hmem =>
        hnotF (Finset.mem_filter.2 ⟨haE, hmem⟩)
      have hV := mk_mem_pairsOn_iff.1 (hE haE)
      have haComp : a ∉ componentOf E V v₀ := by
        intro haC
        have hbC : b ∈ componentOf E V v₀ :=
          componentOf_closed hE ⟨hV.2, haE⟩ haC
        exact hnot (mk_mem_pairsOn_iff.2 ⟨⟨haC, hbC⟩, hV.2⟩)
      have hbComp : b ∉ componentOf E V v₀ := by
        intro hbC
        have haC : a ∈ componentOf E V v₀ :=
          componentOf_closed hE (Adj.symm ⟨hV.2, haE⟩) hbC
        exact haComp haC
      exact mk_mem_pairsOn_iff.2
        ⟨⟨Finset.mem_sdiff.2 ⟨hV.1.1, haComp⟩,
          Finset.mem_sdiff.2 ⟨hV.1.2, hbComp⟩⟩, hV.2⟩

/-- Rebuilding an edge set from a connected piece at `v₀` and a remainder in the
complement: the component of `v₀` is exactly the connected piece. -/
theorem componentOf_union_eq {S : Finset ι} (hv₀ : v₀ ∈ V)
    (hS : S ⊆ V.erase v₀) {E₁ E₂ : Finset (Sym2 ι)}
    (hE₁ : ConnOn (insert v₀ S) E₁)
    (hE₂ : E₂ ⊆ pairsOn (V \ insert v₀ S)) :
    componentOf (E₁ ∪ E₂) V v₀ = insert v₀ S := by
  have hinsV : insert v₀ S ⊆ V := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxS
    · exact hv₀
    · exact Finset.mem_of_mem_erase (hS hxS)
  have hclosed : ∀ ⦃u v : ι⦄, Adj (E₁ ∪ E₂) u v →
      u ∈ insert v₀ S → v ∈ insert v₀ S := by
    intro u v hadj hu
    rcases Finset.mem_union.1 hadj.2 with h1 | h2
    · exact Adj.mem_right_of_subset_pairsOn hE₁.1 ⟨hadj.1, h1⟩
    · exfalso
      have := Adj.mem_left_of_subset_pairsOn hE₂ (⟨hadj.1, h2⟩ : Adj E₂ u v)
      exact (Finset.mem_sdiff.1 this).2 hu
  apply Finset.Subset.antisymm
  · intro v hv
    rcases mem_componentOf.1 hv with ⟨_, hreach⟩
    exact Reach.mem_of_closed hclosed hreach (Finset.mem_insert_self v₀ S)
  · intro u hu
    have hreach : Reach E₁ v₀ u := hE₁.2 v₀ (Finset.mem_insert_self v₀ S) u hu
    exact mem_componentOf.2 ⟨hinsV hu, hreach.mono Finset.subset_union_left⟩

theorem filter_union_pairsOn_eq_left {S : Finset ι} {E₁ E₂ : Finset (Sym2 ι)}
    (hE₁ : E₁ ⊆ pairsOn (insert v₀ S))
    (hE₂ : E₂ ⊆ pairsOn (V \ insert v₀ S)) :
    (E₁ ∪ E₂).filter (fun e => e ∈ pairsOn (insert v₀ S)) = E₁ := by
  classical
  have hdisj : Disjoint (pairsOn (V \ insert v₀ S)) (pairsOn (insert v₀ S)) :=
    disjoint_pairsOn_of_disjoint Finset.sdiff_disjoint
  ext e
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h1 | h2, hp⟩
    · exact h1
    · exact absurd hp (Finset.disjoint_left.1 hdisj (hE₂ h2))
  · intro h
    exact ⟨Or.inl h, hE₁ h⟩

theorem disjoint_edges_of_disjoint_pairsOn {S : Finset ι}
    {E₁ E₂ : Finset (Sym2 ι)}
    (hE₁ : E₁ ⊆ pairsOn (insert v₀ S))
    (hE₂ : E₂ ⊆ pairsOn (V \ insert v₀ S)) :
    Disjoint E₁ E₂ :=
  (disjoint_pairsOn_of_disjoint Finset.disjoint_sdiff).mono hE₁ hE₂

/-- FV (5.7), single-vertex form: the sum of an arbitrary function over all edge
sets on `V` splits according to the connected component of `v₀`. -/
theorem sum_powerset_pairsOn_component_split (hv₀ : v₀ ∈ V)
    (f : Finset (Sym2 ι) → ℝ) :
    ∑ E ∈ (pairsOn V).powerset, f E
      = ∑ S ∈ (V.erase v₀).powerset,
          ∑ E₁ ∈ connGraphsOn (insert v₀ S),
            ∑ E₂ ∈ (pairsOn (V \ insert v₀ S)).powerset, f (E₁ ∪ E₂) := by
  classical
  have hstep :
      ∀ S ∈ (V.erase v₀).powerset,
        (∑ E₁ ∈ connGraphsOn (insert v₀ S),
          ∑ E₂ ∈ (pairsOn (V \ insert v₀ S)).powerset, f (E₁ ∪ E₂))
        = ∑ q ∈ connGraphsOn (insert v₀ S) ×ˢ
              (pairsOn (V \ insert v₀ S)).powerset, f (q.1 ∪ q.2) := by
    intro S _
    rw [Finset.sum_product]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (i := fun E => ⟨(componentOf E V v₀).erase v₀,
      (E.filter fun e => e ∈ pairsOn (componentOf E V v₀),
       E \ E.filter fun e => e ∈ pairsOn (componentOf E V v₀))⟩)
    (j := fun p => p.2.1 ∪ p.2.2) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro E hE
    rw [Finset.mem_powerset] at hE
    have hins : insert v₀ ((componentOf E V v₀).erase v₀) = componentOf E V v₀ :=
      Finset.insert_erase (self_mem_componentOf hv₀)
    rw [Finset.mem_sigma, Finset.mem_product]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Finset.erase_subset_erase v₀ componentOf_subset
    · rw [mem_connGraphsOn, hins]
      exact filter_component_connOn hE hv₀
    · rw [Finset.mem_powerset, hins]
      exact sdiff_filter_component_subset hE
  · -- backward membership
    rintro ⟨S, E₁, E₂⟩ hp
    rw [Finset.mem_sigma, Finset.mem_product] at hp
    obtain ⟨hS, hE₁, hE₂⟩ := hp
    rw [Finset.mem_powerset] at hS hE₂
    rw [mem_connGraphsOn] at hE₁
    rw [Finset.mem_powerset]
    have hinsV : insert v₀ S ⊆ V := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hxS
      · exact hv₀
      · exact Finset.mem_of_mem_erase (hS hxS)
    refine Finset.union_subset ?_ ?_
    · exact hE₁.1.trans (pairsOn_mono hinsV)
    · exact hE₂.trans (pairsOn_mono Finset.sdiff_subset)
  · -- left inverse
    intro E _
    exact Finset.union_sdiff_of_subset (Finset.filter_subset _ E)
  · -- right inverse
    rintro ⟨S, E₁, E₂⟩ hp
    rw [Finset.mem_sigma, Finset.mem_product] at hp
    obtain ⟨hS, hE₁, hE₂⟩ := hp
    rw [Finset.mem_powerset] at hS hE₂
    rw [mem_connGraphsOn] at hE₁
    have hcomp : componentOf (E₁ ∪ E₂) V v₀ = insert v₀ S :=
      componentOf_union_eq hv₀ hS hE₁ hE₂
    have hv₀S : v₀ ∉ S := fun h => Finset.notMem_erase v₀ V (hS h)
    have hfilter : (E₁ ∪ E₂).filter
        (fun e => e ∈ pairsOn (componentOf (E₁ ∪ E₂) V v₀)) = E₁ := by
      rw [hcomp]
      exact filter_union_pairsOn_eq_left hE₁.1 hE₂
    have hsdiff : (E₁ ∪ E₂) \ E₁ = E₂ :=
      Finset.union_sdiff_cancel_left (disjoint_edges_of_disjoint_pairsOn hE₁.1 hE₂)
    dsimp only
    rw [hfilter, hsdiff, hcomp, Finset.erase_insert hv₀S]
  · -- value equality
    intro E _
    rw [Finset.union_sdiff_of_subset (Finset.filter_subset _ E)]

end ComponentSplit

/-! ### The component partition of an edge set -/

open Classical in
/-- The partition of `V` into connected components of the edge set `E`. -/
noncomputable def componentPartitionOn (V : Finset ι) (E : Finset (Sym2 ι)) :
    Finset (Finset ι) :=
  V.image fun v => componentOf E V v

theorem mem_componentPartitionOn {V : Finset ι} {E : Finset (Sym2 ι)}
    {W : Finset ι} :
    W ∈ componentPartitionOn V E ↔ ∃ v ∈ V, componentOf E V v = W := by
  classical
  simp [componentPartitionOn]

theorem componentPartitionOn_mem_partitionsOn {V : Finset ι}
    {E : Finset (Sym2 ι)} (_hE : E ⊆ pairsOn V) :
    componentPartitionOn V E ∈ partitionsOn V := by
  refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨v, hv, rfl⟩ := mem_componentPartitionOn.1 hW
    exact ⟨v, self_mem_componentOf hv⟩
  · intro W hW W' hW' hne
    obtain ⟨v, hv, rfl⟩ := mem_componentPartitionOn.1 hW
    obtain ⟨v', hv', rfl⟩ := mem_componentPartitionOn.1 hW'
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact hne (by
      rw [← componentOf_eq_of_mem hw, ← componentOf_eq_of_mem hw'])
  · apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_sup] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      obtain ⟨v, _, rfl⟩ := mem_componentPartitionOn.1 hW
      exact componentOf_subset hxW
    · intro v hv
      rw [Finset.mem_sup]
      exact ⟨componentOf E V v, mem_componentPartitionOn.2 ⟨v, hv, rfl⟩,
        self_mem_componentOf hv⟩

section ComponentPartitionSplit

variable {V : Finset ι} {v₀ : ι}

/-- Components of a vertex in the complement of the connected piece are
computed within the complement. -/
theorem componentOf_union_of_mem_sdiff {S : Finset ι} (hv₀ : v₀ ∈ V)
    (hS : S ⊆ V.erase v₀) {E₁ E₂ : Finset (Sym2 ι)}
    (hE₁ : ConnOn (insert v₀ S) E₁)
    (hE₂ : E₂ ⊆ pairsOn (V \ insert v₀ S))
    {v : ι} (hv : v ∈ V \ insert v₀ S) :
    componentOf (E₁ ∪ E₂) V v = componentOf E₂ (V \ insert v₀ S) v := by
  have hclosed : ∀ ⦃x y : ι⦄, Adj (E₁ ∪ E₂) x y →
      x ∈ componentOf E₂ (V \ insert v₀ S) v →
      y ∈ componentOf E₂ (V \ insert v₀ S) v := by
    intro x y hadj hx
    rcases mem_componentOf.1 hx with ⟨hxmem, hxreach⟩
    rcases Finset.mem_union.1 hadj.2 with h1 | h2
    · exfalso
      have := Adj.mem_left_of_subset_pairsOn hE₁.1 (⟨hadj.1, h1⟩ : Adj E₁ x y)
      exact (Finset.mem_sdiff.1 hxmem).2 this
    · have hyd : y ∈ V \ insert v₀ S :=
        Adj.mem_right_of_subset_pairsOn hE₂ (⟨hadj.1, h2⟩ : Adj E₂ x y)
      exact mem_componentOf.2 ⟨hyd, hxreach.trans (Adj.reach ⟨hadj.1, h2⟩)⟩
  apply Finset.Subset.antisymm
  · intro w hw
    rcases mem_componentOf.1 hw with ⟨_, hreach⟩
    exact Reach.mem_of_closed hclosed hreach
      (mem_componentOf.2 ⟨hv, Reach.refl v⟩)
  · intro w hw
    rcases mem_componentOf.1 hw with ⟨hwmem, hreach⟩
    exact mem_componentOf.2
      ⟨(Finset.mem_sdiff.1 hwmem).1, hreach.mono Finset.subset_union_right⟩

/-- The component partition of a split edge set: the connected piece at `v₀`
is one block, and the remaining blocks are the components of the remainder. -/
theorem componentPartitionOn_union (hv₀ : v₀ ∈ V) {S : Finset ι}
    (hS : S ⊆ V.erase v₀) {E₁ E₂ : Finset (Sym2 ι)}
    (hE₁ : ConnOn (insert v₀ S) E₁)
    (hE₂ : E₂ ⊆ pairsOn (V \ insert v₀ S)) :
    componentPartitionOn V (E₁ ∪ E₂)
      = insert (insert v₀ S) (componentPartitionOn (V \ insert v₀ S) E₂) := by
  classical
  have hinsV : insert v₀ S ⊆ V := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxS
    · exact hv₀
    · exact Finset.mem_of_mem_erase (hS hxS)
  have hcomp : componentOf (E₁ ∪ E₂) V v₀ = insert v₀ S :=
    componentOf_union_eq hv₀ hS hE₁ hE₂
  have hVsplit : insert v₀ S ∪ V \ insert v₀ S = V :=
    Finset.union_sdiff_of_subset hinsV
  have himage : componentPartitionOn V (E₁ ∪ E₂)
      = ((insert v₀ S) ∪ (V \ insert v₀ S)).image
          (fun v => componentOf (E₁ ∪ E₂) V v) := by
    rw [componentPartitionOn, hVsplit]
  rw [himage, Finset.image_union]
  have himg1 : (insert v₀ S).image (fun v => componentOf (E₁ ∪ E₂) V v)
      = {insert v₀ S} := by
    have hconst : ∀ v ∈ insert v₀ S,
        componentOf (E₁ ∪ E₂) V v = insert v₀ S := by
      intro v hv
      rw [← hcomp] at hv ⊢
      exact componentOf_eq_of_mem hv
    rw [Finset.image_congr (g := fun _ => insert v₀ S) (fun v hv => hconst v hv)]
    exact Finset.image_const (Finset.insert_nonempty v₀ S) _
  have himg2 : (V \ insert v₀ S).image (fun v => componentOf (E₁ ∪ E₂) V v)
      = componentPartitionOn (V \ insert v₀ S) E₂ := by
    rw [componentPartitionOn]
    exact Finset.image_congr fun v hv =>
      componentOf_union_of_mem_sdiff hv₀ hS hE₁ hE₂ hv
  rw [himg1, himg2, Finset.singleton_union]

end ComponentPartitionSplit

/-! ### The fiber identity and the exponential formula (FV Proposition 5.3) -/

/-- The sum of edge-weight products over all edge sets on `V` with a prescribed
component partition `P` factorizes over the blocks of `P`. -/
theorem sum_prod_component_fiber_aux (z : Sym2 ι → ℝ) :
    ∀ (n : ℕ) (V : Finset ι), V.card = n →
      ∀ {P : Finset (Finset ι)}, P ∈ partitionsOn V →
        (∑ E ∈ (pairsOn V).powerset.filter
            (fun E => componentPartitionOn V E = P), ∏ e ∈ E, z e)
          = ∏ W ∈ P, connSum W z := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hcard P hP
    rcases Finset.eq_empty_or_nonempty V with rfl | hVne
    · have hPempty : P = ∅ := by
        have := hP
        rw [partitionsOn_empty, Finset.mem_singleton] at this
        exact this
      subst hPempty
      rw [pairsOn_empty]
      simp [componentPartitionOn]
    · obtain ⟨v₀, hv₀⟩ := hVne
      -- the block of `P` containing `v₀`
      obtain ⟨W₀, ⟨hW₀P, hv₀W₀⟩, hW₀uniq⟩ := exists_unique_block hP hv₀
      have hW₀V : W₀ ⊆ V := block_subset_of_mem_partitionsOn hP hW₀P
      have hW₀ne : W₀.Nonempty := (mem_partitionsOn.1 hP).1 W₀ hW₀P
      -- rewrite the fiber sum through the component split
      rw [Finset.sum_filter,
        sum_powerset_pairsOn_component_split hv₀
          (fun E => if componentPartitionOn V E = P then ∏ e ∈ E, z e else 0)]
      -- only `S = W₀.erase v₀` contributes
      have hvanish : ∀ S ∈ (V.erase v₀).powerset, S ≠ W₀.erase v₀ →
          (∑ E₁ ∈ connGraphsOn (insert v₀ S),
            ∑ E₂ ∈ (pairsOn (V \ insert v₀ S)).powerset,
              if componentPartitionOn V (E₁ ∪ E₂) = P
                then ∏ e ∈ E₁ ∪ E₂, z e else 0) = 0 := by
        intro S hS hSne
        rw [Finset.mem_powerset] at hS
        apply Finset.sum_eq_zero
        intro E₁ hE₁
        apply Finset.sum_eq_zero
        intro E₂ hE₂
        rw [mem_connGraphsOn] at hE₁
        rw [Finset.mem_powerset] at hE₂
        rw [if_neg]
        intro hcpP
        rw [componentPartitionOn_union hv₀ hS hE₁ hE₂] at hcpP
        have hinsP : insert v₀ S ∈ P := by
          rw [← hcpP]; exact Finset.mem_insert_self _ _
        have hinsW₀ : insert v₀ S = W₀ :=
          hW₀uniq (insert v₀ S) ⟨hinsP, Finset.mem_insert_self v₀ S⟩
        apply hSne
        rw [← hinsW₀, Finset.erase_insert (fun h => Finset.notMem_erase v₀ V (hS h))]
      rw [Finset.sum_eq_single_of_mem (W₀.erase v₀)
        (Finset.mem_powerset.2 (Finset.erase_subset_erase v₀ hW₀V)) hvanish]
      -- the surviving term
      have hins : insert v₀ (W₀.erase v₀) = W₀ := Finset.insert_erase hv₀W₀
      rw [hins]
      have hcardlt : (V \ W₀).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.sdiff_ssubset hW₀V hW₀ne)
      have hPerase : P.erase W₀ ∈ partitionsOn (V \ W₀) :=
        erase_mem_partitionsOn_sdiff hP hW₀P
      have hSsub : W₀.erase v₀ ⊆ V.erase v₀ := Finset.erase_subset_erase v₀ hW₀V
      -- transform each summand: split condition and product
      have hsummand : ∀ E₁ ∈ connGraphsOn W₀,
          (∑ E₂ ∈ (pairsOn (V \ W₀)).powerset,
            if componentPartitionOn V (E₁ ∪ E₂) = P
              then ∏ e ∈ E₁ ∪ E₂, z e else 0)
          = (∏ e ∈ E₁, z e) *
              ∑ E₂ ∈ (pairsOn (V \ W₀)).powerset,
                if componentPartitionOn (V \ W₀) E₂ = P.erase W₀
                  then ∏ e ∈ E₂, z e else 0 := by
        intro E₁ hE₁
        rw [mem_connGraphsOn] at hE₁
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun E₂ hE₂ => ?_
        rw [Finset.mem_powerset] at hE₂
        have hE₁' : ConnOn (insert v₀ (W₀.erase v₀)) E₁ := by rw [hins]; exact hE₁
        have hE₂' : E₂ ⊆ pairsOn (V \ insert v₀ (W₀.erase v₀)) := by
          rw [hins]; exact hE₂
        have hcp : componentPartitionOn V (E₁ ∪ E₂)
            = insert W₀ (componentPartitionOn (V \ W₀) E₂) := by
          have := componentPartitionOn_union hv₀ hSsub hE₁' hE₂'
          rw [hins] at this
          exact this
        have hW₀notMem : W₀ ∉ componentPartitionOn (V \ W₀) E₂ := by
          intro hmem
          obtain ⟨v, hv, hveq⟩ := mem_componentPartitionOn.1 hmem
          obtain ⟨x, hx⟩ := hW₀ne
          have : x ∈ componentOf E₂ (V \ W₀) v := hveq.symm ▸ hx
          have hxmem := componentOf_subset this
          exact (Finset.mem_sdiff.1 hxmem).2 hx
        have hcond : (componentPartitionOn V (E₁ ∪ E₂) = P)
            ↔ (componentPartitionOn (V \ W₀) E₂ = P.erase W₀) := by
          rw [hcp]
          constructor
          · intro h
            rw [← h, Finset.erase_insert hW₀notMem]
          · intro h
            rw [h, Finset.insert_erase hW₀P]
        have hdisjE : Disjoint E₁ E₂ :=
          (disjoint_pairsOn_of_disjoint Finset.disjoint_sdiff).mono hE₁.1 hE₂
        rw [if_congr hcond rfl rfl, Finset.prod_union hdisjE, mul_ite, mul_zero]
      rw [Finset.sum_congr rfl hsummand, ← Finset.sum_mul, ← Finset.sum_filter,
        ih ((V \ W₀).card) hcardlt (V \ W₀) rfl hPerase]
      rw [show (∑ E ∈ connGraphsOn W₀, ∏ e ∈ E, z e) = connSum W₀ z from rfl]
      exact Finset.mul_prod_erase P (fun W => connSum W z) hW₀P

/-- The fiber identity: the sum of edge-weight products over all edge sets on
`V` whose component partition is `P` equals the product over the blocks of `P`
of the connected sums. -/
theorem sum_prod_component_fiber (z : Sym2 ι → ℝ) {V : Finset ι}
    {P : Finset (Finset ι)} (hP : P ∈ partitionsOn V) :
    (∑ E ∈ (pairsOn V).powerset.filter
        (fun E => componentPartitionOn V E = P), ∏ e ∈ E, z e)
      = ∏ W ∈ P, connSum W z :=
  sum_prod_component_fiber_aux z V.card V rfl hP

/-- The exponential formula, graph side (FV Proposition 5.3): the full graph sum
on `V` is the sum over partitions of `V` of the product of connected sums over
the blocks. -/
theorem graphSum_eq_sum_partitions (z : Sym2 ι → ℝ) (V : Finset ι) :
    graphSum V z = ∑ P ∈ partitionsOn V, ∏ W ∈ P, connSum W z := by
  classical
  rw [graphSum,
    ← Finset.sum_fiberwise_of_maps_to
      (g := fun E => componentPartitionOn V E)
      (fun E hE =>
        componentPartitionOn_mem_partitionsOn (Finset.mem_powerset.1 hE))
      (fun E => ∏ e ∈ E, z e)]
  exact Finset.sum_congr rfl fun P hP => sum_prod_component_fiber z hP

/-! ### The star decomposition (FV (5.13)) -/

section StarDecomposition

variable {V : Finset ι} {v₀ : ι}

theorem star_injOn (hv₀ : v₀ ∉ V) :
    Set.InjOn (fun u => s(v₀, u)) (V : Set ι) := by
  intro u hu u' hu' h
  have h' : s(v₀, u) = s(v₀, u') := h
  exact Sym2.congr_right.1 h'

theorem star_notMem_pairsOn (hv₀ : v₀ ∉ V) (u : ι) :
    s(v₀, u) ∉ pairsOn V := by
  intro h
  exact hv₀ (mk_mem_pairsOn_iff.1 h).1.1

theorem notMem_of_mem_pairsOn (hv₀ : v₀ ∉ V) {e : Sym2 ι}
    (he : e ∈ pairsOn V) : v₀ ∉ e := by
  intro hmem
  induction e with
  | _ a b =>
      rcases Sym2.mem_iff.1 hmem with rfl | rfl
      · exact hv₀ (mk_mem_pairsOn_iff.1 he).1.1
      · exact hv₀ (mk_mem_pairsOn_iff.1 he).1.2

/-- Connectivity of a star-plus-remainder edge set on `insert v₀ V` is
equivalent to every component of the remainder being hit by a star edge. -/
theorem connOn_insert_iff_hits (hv₀ : v₀ ∉ V) {Er : Finset (Sym2 ι)}
    {K : Finset ι} (hEr : Er ⊆ pairsOn V) (hK : K ⊆ V) :
    ConnOn (insert v₀ V) (Er ∪ K.image fun u => s(v₀, u)) ↔
      ∀ W ∈ componentPartitionOn V Er, (K ∩ W).Nonempty := by
  classical
  set E : Finset (Sym2 ι) := Er ∪ K.image (fun u => s(v₀, u)) with hE
  have hEsub : E ⊆ pairsOn (insert v₀ V) := by
    intro e he
    rcases Finset.mem_union.1 he with h1 | h2
    · exact pairsOn_mono (Finset.subset_insert v₀ V) (hEr h1)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h2
      exact mk_mem_pairsOn_iff.2
        ⟨⟨Finset.mem_insert_self v₀ V, Finset.mem_insert_of_mem (hK hu)⟩,
          fun h => hv₀ (h ▸ hK hu)⟩
  constructor
  · -- connectivity forces every component to be hit
    intro hconn W hW
    obtain ⟨w, hwV, rfl⟩ := mem_componentPartitionOn.1 hW
    have hreach : Reach E v₀ w :=
      hconn.2 v₀ (Finset.mem_insert_self v₀ V) w (Finset.mem_insert_of_mem hwV)
    -- vertices reachable from `v₀` are `v₀` or lie in a hit component
    have hp : ∀ x, Reach E v₀ x →
        (x = v₀ ∨ ∃ k ∈ K, x ∈ componentOf Er V k) := by
      intro x hx
      refine Reach.mem_of_closed
        (p := fun x => x = v₀ ∨ ∃ k ∈ K, x ∈ componentOf Er V k) ?_ hx (Or.inl rfl)
      intro a b hadj hpa
      rcases Finset.mem_union.1 hadj.2 with h1 | h2
      · -- remainder edge: stay in the same component (or contradict `a = v₀`)
        rcases hpa with rfl | ⟨k, hk, hak⟩
        · exact absurd (Adj.mem_left_of_subset_pairsOn hEr ⟨hadj.1, h1⟩) hv₀
        · exact Or.inr ⟨k, hk, componentOf_closed hEr ⟨hadj.1, h1⟩ hak⟩
      · -- star edge: move to `v₀` or into the component of a star target
        obtain ⟨u, hu, huv⟩ := Finset.mem_image.1 h2
        have huv' : s(v₀, u) = s(a, b) := huv
        rcases Sym2.eq_iff.1 huv' with ⟨_, hb⟩ | ⟨hb, _⟩
        · -- v₀ = a and u = b
          subst hb
          exact Or.inr ⟨u, hu, self_mem_componentOf (hK hu)⟩
        · -- v₀ = b and u = a
          exact Or.inl hb.symm
    rcases hp w hreach with rfl | ⟨k, hk, hwk⟩
    · exact absurd hwV hv₀
    · refine ⟨k, Finset.mem_inter.2 ⟨hk, ?_⟩⟩
      rw [componentOf_eq_of_mem hwk]
      exact self_mem_componentOf (hK hk)
  · -- hitting all components gives connectivity
    intro hhits
    refine ⟨hEsub, ?_⟩
    have hreach : ∀ x ∈ insert v₀ V, Reach E v₀ x := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hxV
      · exact Reach.refl x
      · have hWmem : componentOf Er V x ∈ componentPartitionOn V Er :=
          mem_componentPartitionOn.2 ⟨x, hxV, rfl⟩
        obtain ⟨k, hkmem⟩ := hhits _ hWmem
        rcases Finset.mem_inter.1 hkmem with ⟨hkK, hkW⟩
        have h1 : Reach E v₀ k := by
          refine Adj.reach ⟨fun h => hv₀ (h ▸ hK hkK), ?_⟩
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkK)
        have h2 : Reach Er x k := (mem_componentOf.1 hkW).2
        exact h1.trans ((h2.mono Finset.subset_union_left).symm)
    intro u hu v hv
    exact (hreach u hu).symm.trans (hreach v hv)

/-- Factorization of the sum over subsets hitting every block of a partition:
each block contributes `∏ (1 + y) - 1` (the sum over its nonempty subsets). -/
theorem sum_hitting_subsets_aux (y : ι → ℝ) :
    ∀ (n : ℕ) (V : Finset ι), V.card = n →
      ∀ {P : Finset (Finset ι)}, P ∈ partitionsOn V →
      (∑ K ∈ V.powerset.filter (fun K => ∀ W ∈ P, (K ∩ W).Nonempty),
          ∏ u ∈ K, y u)
        = ∏ W ∈ P, ((∏ u ∈ W, (1 + y u)) - 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hcard P hP
    rcases Finset.eq_empty_or_nonempty P with rfl | hPne
    · -- no blocks: `V = ∅`, only `K = ∅` contributes
      have hVempty : V = ∅ := by
        have := (mem_partitionsOn.1 hP).2.2
        simpa using this.symm
      subst hVempty
      simp
    · obtain ⟨W₀, hW₀P⟩ := hPne
      have hW₀V : W₀ ⊆ V := block_subset_of_mem_partitionsOn hP hW₀P
      have hW₀ne : W₀.Nonempty := (mem_partitionsOn.1 hP).1 W₀ hW₀P
      have hPerase : P.erase W₀ ∈ partitionsOn (V \ W₀) :=
        erase_mem_partitionsOn_sdiff hP hW₀P
      have hcardlt : (V \ W₀).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.sdiff_ssubset hW₀V hW₀ne)
      -- split `K` into its intersections with `W₀` and with `V \ W₀`
      have hbij :
          (∑ K ∈ V.powerset.filter (fun K => ∀ W ∈ P, (K ∩ W).Nonempty),
            ∏ u ∈ K, y u)
          = ∑ q ∈ (W₀.powerset.filter (fun K₀ => K₀.Nonempty)) ×ˢ
                ((V \ W₀).powerset.filter
                  (fun K' => ∀ W ∈ P.erase W₀, (K' ∩ W).Nonempty)),
              (∏ u ∈ q.1, y u) * ∏ u ∈ q.2, y u := by
        refine Finset.sum_nbij' (i := fun K => (K ∩ W₀, K \ W₀))
          (j := fun q => q.1 ∪ q.2) ?_ ?_ ?_ ?_ ?_
        · -- forward membership
          intro K hK
          rw [Finset.mem_filter, Finset.mem_powerset] at hK
          obtain ⟨hKV, hKhits⟩ := hK
          rw [Finset.mem_product]
          constructor
          · rw [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.inter_subset_right, hKhits W₀ hW₀P⟩
          · rw [Finset.mem_filter, Finset.mem_powerset]
            constructor
            · intro x hx
              rcases Finset.mem_sdiff.1 hx with ⟨hxK, hxW₀⟩
              exact Finset.mem_sdiff.2 ⟨hKV hxK, hxW₀⟩
            · intro W hW
              obtain ⟨x, hx⟩ := hKhits W (Finset.mem_of_mem_erase hW)
              rcases Finset.mem_inter.1 hx with ⟨hxK, hxW⟩
              refine ⟨x, Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hxK, ?_⟩, hxW⟩⟩
              intro hxW₀
              have hWP := Finset.mem_of_mem_erase hW
              have hWne := Finset.ne_of_mem_erase hW
              exact Finset.disjoint_left.1
                ((mem_partitionsOn.1 hP).2.1 hWP hW₀P hWne) hxW hxW₀
        · -- backward membership
          rintro ⟨K₀, K'⟩ hq
          rw [Finset.mem_product] at hq
          obtain ⟨h₀, h'⟩ := hq
          rw [Finset.mem_filter, Finset.mem_powerset] at h₀ h'
          rw [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · exact Finset.union_subset (h₀.1.trans hW₀V)
              (h'.1.trans Finset.sdiff_subset)
          · intro W hW
            by_cases hWeq : W = W₀
            · subst hWeq
              obtain ⟨x, hx⟩ := h₀.2
              exact ⟨x, Finset.mem_inter.2
                ⟨Finset.mem_union_left _ hx, h₀.1 hx⟩⟩
            · obtain ⟨x, hx⟩ := h'.2 W (Finset.mem_erase.2 ⟨hWeq, hW⟩)
              rcases Finset.mem_inter.1 hx with ⟨hxK', hxW⟩
              exact ⟨x, Finset.mem_inter.2
                ⟨Finset.mem_union_right _ hxK', hxW⟩⟩
        · -- left inverse
          intro K hK
          rw [Finset.mem_filter, Finset.mem_powerset] at hK
          dsimp only
          rw [Finset.union_comm, Finset.sdiff_union_inter]
        · -- right inverse
          rintro ⟨K₀, K'⟩ hq
          rw [Finset.mem_product] at hq
          obtain ⟨h₀, h'⟩ := hq
          rw [Finset.mem_filter, Finset.mem_powerset] at h₀ h'
          have hdisj : Disjoint K' W₀ := by
            rw [Finset.disjoint_left]
            intro x hxK' hxW₀
            exact (Finset.mem_sdiff.1 (h'.1 hxK')).2 hxW₀
          have h1 : (K₀ ∪ K') ∩ W₀ = K₀ := by
            rw [Finset.union_inter_distrib_right,
              Finset.inter_eq_left.2 h₀.1,
              Finset.disjoint_iff_inter_eq_empty.1 hdisj, Finset.union_empty]
          have h2 : (K₀ ∪ K') \ W₀ = K' := by
            rw [Finset.union_sdiff_distrib,
              Finset.sdiff_eq_empty_iff_subset.2 h₀.1,
              Finset.sdiff_eq_self_of_disjoint hdisj, Finset.empty_union]
          dsimp only
          rw [h1, h2]
        · -- values
          intro K hK
          rw [Finset.mem_filter, Finset.mem_powerset] at hK
          dsimp only
          rw [← Finset.prod_union (Finset.disjoint_sdiff_inter K W₀).symm,
            Finset.union_comm, Finset.sdiff_union_inter]
      rw [hbij, Finset.sum_product]
      have hinner : ∀ K₀,
          (∑ K' ∈ (V \ W₀).powerset.filter
              (fun K' => ∀ W ∈ P.erase W₀, (K' ∩ W).Nonempty),
            (∏ u ∈ K₀, y u) * ∏ u ∈ K', y u)
          = (∏ u ∈ K₀, y u) * ∏ W ∈ P.erase W₀, ((∏ u ∈ W, (1 + y u)) - 1) := by
        intro K₀
        rw [← Finset.mul_sum, ih ((V \ W₀).card) hcardlt (V \ W₀) rfl hPerase]
      rw [Finset.sum_congr rfl fun K₀ _ => hinner K₀, ← Finset.sum_mul]
      have hstar : (∑ K₀ ∈ W₀.powerset.filter (fun K₀ => K₀.Nonempty),
          ∏ u ∈ K₀, y u) = (∏ u ∈ W₀, (1 + y u)) - 1 := by
        have hfull : (∑ K₀ ∈ W₀.powerset, ∏ u ∈ K₀, y u)
            = ∏ u ∈ W₀, (1 + y u) := (Finset.prod_one_add W₀).symm
        have hemptyfilter :
            W₀.powerset.filter (fun K₀ => ¬ K₀.Nonempty) = {∅} := by
          ext K₀
          rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
            Finset.not_nonempty_iff_eq_empty]
          constructor
          · rintro ⟨_, rfl⟩; rfl
          · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
        have hsplit : (∑ K₀ ∈ W₀.powerset, ∏ u ∈ K₀, y u)
            = (∑ K₀ ∈ W₀.powerset.filter (fun K₀ => K₀.Nonempty),
                ∏ u ∈ K₀, y u) + 1 := by
          rw [← Finset.sum_filter_add_sum_filter_not W₀.powerset
            (fun K₀ => K₀.Nonempty)]
          congr 1
          rw [hemptyfilter, Finset.sum_singleton, Finset.prod_empty]
        rw [hsplit] at hfull
        linarith
      rw [hstar]
      exact Finset.mul_prod_erase P (fun W => (∏ u ∈ W, (1 + y u)) - 1) hW₀P

theorem sum_hitting_subsets (y : ι → ℝ) {V : Finset ι}
    {P : Finset (Finset ι)} (hP : P ∈ partitionsOn V) :
    (∑ K ∈ V.powerset.filter (fun K => ∀ W ∈ P, (K ∩ W).Nonempty),
        ∏ u ∈ K, y u)
      = ∏ W ∈ P, ((∏ u ∈ W, (1 + y u)) - 1) :=
  sum_hitting_subsets_aux y V.card V rfl hP

theorem filter_notMem_subset_pairsOn (hv₀ : v₀ ∉ V) {E : Finset (Sym2 ι)}
    (hE : E ⊆ pairsOn (insert v₀ V)) :
    E.filter (fun e => v₀ ∉ e) ⊆ pairsOn V := by
  classical
  intro e
  induction e with
  | _ a b =>
      intro he
      rcases Finset.mem_filter.1 he with ⟨heE, hv₀e⟩
      have h := mk_mem_pairsOn_iff.1 (hE heE)
      rw [Sym2.mem_iff] at hv₀e
      push_neg at hv₀e
      have ha : a ∈ V := by
        rcases Finset.mem_insert.1 h.1.1 with rfl | haV
        · exact absurd rfl hv₀e.1
        · exact haV
      have hb : b ∈ V := by
        rcases Finset.mem_insert.1 h.1.2 with rfl | hbV
        · exact absurd rfl hv₀e.2
        · exact hbV
      exact mk_mem_pairsOn_iff.2 ⟨⟨ha, hb⟩, h.2⟩

/-- Every edge set on `insert v₀ V` is the disjoint union of its `v₀`-free part
and the star of its `v₀`-neighbours. -/
theorem eq_filter_union_star (hv₀ : v₀ ∉ V) {E : Finset (Sym2 ι)}
    (hE : E ⊆ pairsOn (insert v₀ V)) :
    E = E.filter (fun e => v₀ ∉ e)
        ∪ (V.filter fun u => s(v₀, u) ∈ E).image (fun u => s(v₀, u)) := by
  classical
  ext e
  constructor
  · intro he
    by_cases hv₀e : v₀ ∈ e
    · obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₀e
      have h := mk_mem_pairsOn_iff.1 (hE he)
      have huV : u ∈ V := by
        rcases Finset.mem_insert.1 h.1.2 with rfl | huV
        · exact absurd rfl h.2
        · exact huV
      exact Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨huV, he⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hv₀e⟩)
  · intro he
    rcases Finset.mem_union.1 he with h1 | h2
    · exact Finset.mem_filter.1 h1 |>.1
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h2
      exact (Finset.mem_filter.1 hu).2

theorem disjoint_filter_star (hv₀ : v₀ ∉ V) {Er : Finset (Sym2 ι)}
    (hEr : Er ⊆ pairsOn V) (K : Finset ι) :
    Disjoint Er (K.image fun u => s(v₀, u)) := by
  classical
  rw [Finset.disjoint_left]
  intro e heEr heK
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 heK
  exact notMem_of_mem_pairsOn hv₀ (hEr heEr) (Sym2.mem_mk_left v₀ u)

/-- The star decomposition of connected sums (FV (5.13)): a connected graph on
`insert v₀ V` is a partition of `V` into connected blocks together with a
nonempty star from `v₀` into each block. -/
theorem connSum_insert (z : Sym2 ι → ℝ) {V : Finset ι} {v₀ : ι} (hv₀ : v₀ ∉ V) :
    connSum (insert v₀ V) z
      = ∑ P ∈ partitionsOn V,
          (∏ W ∈ P, connSum W z) *
            ∏ W ∈ P, ((∏ u ∈ W, (1 + z s(v₀, u))) - 1) := by
  classical
  -- Step 1: bijection with pairs (remainder, star targets)
  have hstep1 : connSum (insert v₀ V) z
      = ∑ q ∈ ((pairsOn V).powerset ×ˢ V.powerset).filter
            (fun q => ∀ W ∈ componentPartitionOn V q.1, (q.2 ∩ W).Nonempty),
          (∏ e ∈ q.1, z e) * ∏ u ∈ q.2, z s(v₀, u) := by
    refine Finset.sum_nbij'
      (i := fun E => (E.filter (fun e => v₀ ∉ e),
        V.filter (fun u => s(v₀, u) ∈ E)))
      (j := fun q => q.1 ∪ q.2.image (fun u => s(v₀, u))) ?_ ?_ ?_ ?_ ?_
    · -- forward membership
      intro E hE
      rw [mem_connGraphsOn] at hE
      have hEr := filter_notMem_subset_pairsOn hv₀ hE.1
      have hK : V.filter (fun u => s(v₀, u) ∈ E) ⊆ V := Finset.filter_subset _ V
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_powerset.2 hEr, Finset.mem_powerset.2 hK⟩, ?_⟩
      have hconn : ConnOn (insert v₀ V)
          (E.filter (fun e => v₀ ∉ e)
            ∪ (V.filter fun u => s(v₀, u) ∈ E).image (fun u => s(v₀, u))) := by
        rw [← eq_filter_union_star hv₀ hE.1]
        exact hE
      exact (connOn_insert_iff_hits hv₀ hEr hK).1 hconn
    · -- backward membership
      rintro ⟨Er, K⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hEr, hK⟩, hhits⟩ := hq
      rw [Finset.mem_powerset] at hEr hK
      rw [mem_connGraphsOn]
      exact (connOn_insert_iff_hits hv₀ hEr hK).2 hhits
    · -- left inverse
      intro E hE
      rw [mem_connGraphsOn] at hE
      exact (eq_filter_union_star hv₀ hE.1).symm
    · -- right inverse
      rintro ⟨Er, K⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hEr, hK⟩, _⟩ := hq
      rw [Finset.mem_powerset] at hEr hK
      dsimp only
      have h1 : (Er ∪ K.image fun u => s(v₀, u)).filter (fun e => v₀ ∉ e)
          = Er := by
        rw [Finset.filter_union]
        have hEr' : Er.filter (fun e => v₀ ∉ e) = Er :=
          Finset.filter_true_of_mem fun e he =>
            notMem_of_mem_pairsOn hv₀ (hEr he)
        have hst : (K.image fun u => s(v₀, u)).filter (fun e => v₀ ∉ e)
            = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e he
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 he
          intro hcon
          exact hcon (Sym2.mem_mk_left v₀ u)
        rw [hEr', hst, Finset.union_empty]
      have h2 : V.filter
          (fun u => s(v₀, u) ∈ Er ∪ K.image fun u' => s(v₀, u')) = K := by
        ext u
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨huV, humem⟩
          rcases Finset.mem_union.1 humem with hcon | himg
          · exact absurd hcon (star_notMem_pairsOn hv₀ u ∘ fun h => hEr h)
          · obtain ⟨k, hk, hks⟩ := Finset.mem_image.1 himg
            have : s(v₀, k) = s(v₀, u) := hks
            rw [Sym2.congr_right.1 this] at hk
            exact hk
        · intro hu
          exact ⟨hK hu, Finset.mem_union_right _
            (Finset.mem_image_of_mem _ hu)⟩
      rw [h1, h2]
    · -- values
      intro E hE
      rw [mem_connGraphsOn] at hE
      have hEr := filter_notMem_subset_pairsOn hv₀ hE.1
      conv_lhs => rw [eq_filter_union_star hv₀ hE.1]
      rw [Finset.prod_union (disjoint_filter_star hv₀ hEr _)]
      congr 1
      rw [Finset.prod_image]
      intro x hx y hy hxy
      exact star_injOn hv₀ ((Finset.mem_filter.1 hx).1)
        ((Finset.mem_filter.1 hy).1) hxy
  rw [hstep1]
  -- Step 2: unfold the product-filter into nested sums
  rw [Finset.sum_filter, Finset.sum_product]
  -- Step 3+4: inner star sums factor over the components of the remainder
  have hinner : ∀ Er ∈ (pairsOn V).powerset,
      (∑ K ∈ V.powerset,
        if ∀ W ∈ componentPartitionOn V Er, (K ∩ W).Nonempty
          then (∏ e ∈ Er, z e) * ∏ u ∈ K, z s(v₀, u) else 0)
      = (∏ e ∈ Er, z e) *
          ∏ W ∈ componentPartitionOn V Er,
            ((∏ u ∈ W, (1 + z s(v₀, u))) - 1) := by
    intro Er hEr
    rw [Finset.mem_powerset] at hEr
    have hcp := componentPartitionOn_mem_partitionsOn (V := V) (E := Er) hEr
    calc
      (∑ K ∈ V.powerset,
        if ∀ W ∈ componentPartitionOn V Er, (K ∩ W).Nonempty
          then (∏ e ∈ Er, z e) * ∏ u ∈ K, z s(v₀, u) else 0)
        = ∑ K ∈ V.powerset.filter
              (fun K => ∀ W ∈ componentPartitionOn V Er, (K ∩ W).Nonempty),
            (∏ e ∈ Er, z e) * ∏ u ∈ K, z s(v₀, u) := by
          rw [Finset.sum_filter]
      _ = (∏ e ∈ Er, z e) *
            ∑ K ∈ V.powerset.filter
              (fun K => ∀ W ∈ componentPartitionOn V Er, (K ∩ W).Nonempty),
              ∏ u ∈ K, z s(v₀, u) := by
          rw [Finset.mul_sum]
      _ = (∏ e ∈ Er, z e) *
            ∏ W ∈ componentPartitionOn V Er,
              ((∏ u ∈ W, (1 + z s(v₀, u))) - 1) := by
          rw [sum_hitting_subsets (fun u => z s(v₀, u)) hcp]
  rw [Finset.sum_congr rfl hinner]
  -- Step 5: group the remainder sum by its component partition
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun Er => componentPartitionOn V Er)
    (fun Er hEr =>
      componentPartitionOn_mem_partitionsOn (Finset.mem_powerset.1 hEr))
    (fun Er => (∏ e ∈ Er, z e) *
      ∏ W ∈ componentPartitionOn V Er, ((∏ u ∈ W, (1 + z s(v₀, u))) - 1))]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hfiber : ∀ Er ∈ (pairsOn V).powerset.filter
      (fun Er => componentPartitionOn V Er = P),
      (∏ e ∈ Er, z e) *
          ∏ W ∈ componentPartitionOn V Er,
            ((∏ u ∈ W, (1 + z s(v₀, u))) - 1)
        = (∏ e ∈ Er, z e) *
            ∏ W ∈ P, ((∏ u ∈ W, (1 + z s(v₀, u))) - 1) := by
    intro Er hEr
    rw [(Finset.mem_filter.1 hEr).2]
  rw [Finset.sum_congr rfl hfiber, ← Finset.sum_mul,
    sum_prod_component_fiber z hP]

end StarDecomposition

/-! ### Relabeling invariance -/

section Relabel

variable {κ : Type*} [DecidableEq κ]

/-- The `Sym2`-embedding induced by an embedding of vertex types. -/
def sym2Emb (σ : ι ↪ κ) : Sym2 ι ↪ Sym2 κ :=
  ⟨Sym2.map σ, Sym2.map.injective σ.injective⟩

theorem sym2Emb_mk (σ : ι ↪ κ) (a b : ι) :
    sym2Emb σ s(a, b) = s(σ a, σ b) := rfl

theorem pairsOn_map (σ : ι ↪ κ) (V : Finset ι) :
    pairsOn (V.map σ) = (pairsOn V).map (sym2Emb σ) := by
  ext e
  induction e with
  | _ x y =>
      rw [mk_mem_pairsOn_iff]
      constructor
      · rintro ⟨⟨hx, hy⟩, hxy⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
        refine Finset.mem_map.2 ⟨s(a, b), ?_, rfl⟩
        exact mk_mem_pairsOn_iff.2 ⟨⟨ha, hb⟩, fun h => hxy (congrArg σ h)⟩
      · intro h
        obtain ⟨e, he, heq⟩ := Finset.mem_map.1 h
        induction e with
        | _ a b =>
            have h' := mk_mem_pairsOn_iff.1 he
            have : s(σ a, σ b) = s(x, y) := heq
            rcases Sym2.eq_iff.1 this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨⟨Finset.mem_map_of_mem σ h'.1.1,
                Finset.mem_map_of_mem σ h'.1.2⟩,
                fun h'' => h'.2 (σ.injective h'')⟩
            · exact ⟨⟨Finset.mem_map_of_mem σ h'.1.2,
                Finset.mem_map_of_mem σ h'.1.1⟩,
                fun h'' => h'.2 (σ.injective h''.symm)⟩

theorem adj_map_iff (σ : ι ↪ κ) {E : Finset (Sym2 ι)} {a b : ι} :
    Adj (E.map (sym2Emb σ)) (σ a) (σ b) ↔ Adj E a b := by
  constructor
  · rintro ⟨hne, hmem⟩
    obtain ⟨e, he, heq⟩ := Finset.mem_map.1 hmem
    induction e with
    | _ a' b' =>
        have : s(σ a', σ b') = s(σ a, σ b) := heq
        rcases Sym2.eq_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [σ.injective h1, σ.injective h2] at he
          exact ⟨fun h => hne (congrArg σ h), he⟩
        · rw [σ.injective h1, σ.injective h2] at he
          rw [Sym2.eq_swap] at he
          exact ⟨fun h => hne (congrArg σ h), he⟩
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (σ.injective h),
      by rw [← sym2Emb_mk]; exact Finset.mem_map_of_mem _ hmem⟩

theorem reach_map_of_reach (σ : ι ↪ κ) {E : Finset (Sym2 ι)} {a b : ι}
    (h : Reach E a b) : Reach (E.map (sym2Emb σ)) (σ a) (σ b) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hadj ih =>
      exact Relation.ReflTransGen.tail ih ((adj_map_iff σ).2 hadj)

theorem reach_map_reflect (σ : ι ↪ κ) {E : Finset (Sym2 ι)} {V : Finset ι}
    (hE : E ⊆ pairsOn V) {a : ι} {w : κ}
    (h : Reach (E.map (sym2Emb σ)) (σ a) w) :
    ∃ b, w = σ b ∧ Reach E a b := by
  have hmain : ∀ x, Reach (E.map (sym2Emb σ)) (σ a) x →
      ∃ b, x = σ b ∧ Reach E a b := by
    intro x hx
    refine Reach.mem_of_closed (p := fun x => ∃ b, x = σ b ∧ Reach E a b)
      ?_ hx ⟨a, rfl, Reach.refl a⟩
    rintro u v hadj ⟨b, rfl, hb⟩
    obtain ⟨e, he, heq⟩ := Finset.mem_map.1 hadj.2
    induction e with
    | _ a' b' =>
        have heq' : s(σ a', σ b') = s(σ b, v) := heq
        rcases Sym2.eq_iff.1 heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- σ a' = σ b and σ b' = v
          have ha'b : a' = b := σ.injective h1
          subst ha'b
          refine ⟨b', h2.symm, hb.trans (Adj.reach ⟨?_, he⟩)⟩
          intro hcon
          exact hadj.1 (by rw [hcon, h2])
        · -- σ a' = v and σ b' = σ b
          have hb'b : b' = b := σ.injective h2
          subst hb'b
          refine ⟨a', h1.symm, hb.trans (Adj.reach ⟨?_, ?_⟩)⟩
          · intro hcon
            exact hadj.1 (by rw [hcon, h1])
          · rw [Sym2.eq_swap] at he
            exact he
  exact hmain w h

theorem connOn_map_iff (σ : ι ↪ κ) {V : Finset ι} {E : Finset (Sym2 ι)} :
    ConnOn (V.map σ) (E.map (sym2Emb σ)) ↔ ConnOn V E := by
  constructor
  · rintro ⟨hsub, hconn⟩
    have hE : E ⊆ pairsOn V := by
      rw [pairsOn_map] at hsub
      exact (Finset.map_subset_map).1 hsub
    refine ⟨hE, ?_⟩
    intro a ha b hb
    have := hconn (σ a) (Finset.mem_map_of_mem σ ha)
      (σ b) (Finset.mem_map_of_mem σ hb)
    obtain ⟨b', hb', hreach⟩ := reach_map_reflect σ hE this
    rw [← σ.injective hb'] at hreach
    exact hreach
  · rintro ⟨hsub, hconn⟩
    constructor
    · rw [pairsOn_map]
      exact Finset.map_subset_map.2 hsub
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      exact reach_map_of_reach σ (hconn a ha b hb)

/-- Relabeling invariance of connected sums along an embedding of the vertex
type. -/
theorem connSum_map (σ : ι ↪ κ) (V : Finset ι) (z : Sym2 κ → ℝ) :
    connSum (V.map σ) z = connSum V (fun e => z (Sym2.map σ e)) := by
  classical
  refine (Finset.sum_nbij (i := fun E => E.map (sym2Emb σ))
    ?_ ?_ ?_ ?_).symm
  · -- membership
    intro E hE
    rw [mem_connGraphsOn] at hE ⊢
    exact (connOn_map_iff σ).2 hE
  · -- injectivity
    intro E₁ _ E₂ _ h
    exact Finset.map_injective (sym2Emb σ) h
  · -- surjectivity
    intro E' hE'
    rw [Finset.mem_coe, mem_connGraphsOn] at hE'
    have hsub : E' ⊆ (pairsOn V).map (sym2Emb σ) := by
      rw [← pairsOn_map]
      exact hE'.1
    obtain ⟨E, _, rfl⟩ := Finset.subset_map_iff.1 hsub
    refine ⟨E, ?_, rfl⟩
    rw [Finset.mem_coe, mem_connGraphsOn]
    exact (connOn_map_iff σ).1 hE'
  · -- values
    intro E _
    rw [Finset.prod_map]
    rfl

theorem image_map_mem_partitionsOn (σ : ι ↪ κ) {V : Finset ι}
    {P : Finset (Finset ι)} (hP : P ∈ partitionsOn V) :
    P.image (fun W => W.map σ) ∈ partitionsOn (V.map σ) := by
  classical
  obtain ⟨hne, hdisj, hsup⟩ := mem_partitionsOn.1 hP
  refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
  · intro Wb hWb
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hWb
    exact (hne W hW).map
  · intro Wb hWb Wb' hWb' hne'
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hWb
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.1 hWb'
    have hWne : W ≠ W' := fun h => hne' (by rw [h])
    exact (Finset.disjoint_map σ).2 (hdisj hW hW' hWne)
  · ext x
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨Wb, hWb, hxWb⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hWb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hxWb
      refine Finset.mem_map_of_mem σ ?_
      rw [← hsup, Finset.mem_sup]
      exact ⟨W, hW, ha⟩
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      rw [← hsup, Finset.mem_sup] at ha
      obtain ⟨W, hW, haW⟩ := ha
      exact ⟨W.map σ, Finset.mem_image_of_mem _ hW, Finset.mem_map_of_mem σ haW⟩

/-- Transport of partition sums along an embedding of the vertex type. -/
theorem sum_partitionsOn_map {M : Type*} [AddCommMonoid M] (σ : ι ↪ κ)
    (V : Finset ι) (F : Finset (Finset κ) → M) :
    ∑ Pa ∈ partitionsOn (V.map σ), F Pa
      = ∑ P ∈ partitionsOn V, F (P.image fun W => W.map σ) := by
  classical
  refine (Finset.sum_nbij (i := fun P => P.image fun W => W.map σ)
    ?_ ?_ ?_ ?_).symm
  · intro P hP
    exact image_map_mem_partitionsOn σ hP
  · intro P₁ _ P₂ _ h
    have : Function.Injective fun W : Finset ι => W.map σ :=
      fun _ _ hWW => Finset.map_injective σ hWW
    exact Finset.image_injective this h
  · intro Pa hPa
    rw [Finset.mem_coe] at hPa
    have hblocks : ∀ Wb ∈ Pa, ∃ U : Finset ι, U ⊆ V ∧ U.map σ = Wb := by
      intro Wb hWb
      have := block_subset_of_mem_partitionsOn hPa hWb
      obtain ⟨U, hU, rfl⟩ := Finset.subset_map_iff.1 this
      exact ⟨U, hU, rfl⟩
    refine ⟨Pa.image (fun Wb => Wb.preimage σ σ.injective.injOn), ?_, ?_⟩
    · rw [Finset.mem_coe]
      obtain ⟨hne, hdisj, hsup⟩ := mem_partitionsOn.1 hPa
      refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
      · intro U hU
        obtain ⟨Wb, hWb, rfl⟩ := Finset.mem_image.1 hU
        obtain ⟨U', _, rfl⟩ := hblocks Wb hWb
        rw [Finset.preimage_map]
        exact (Finset.map_nonempty).1 (hne _ hWb)
      · intro U hU U' hU' hne'
        obtain ⟨Wb, hWb, rfl⟩ := Finset.mem_image.1 hU
        obtain ⟨Wb', hWb', rfl⟩ := Finset.mem_image.1 hU'
        obtain ⟨U₀, _, rfl⟩ := hblocks Wb hWb
        obtain ⟨U₀', _, rfl⟩ := hblocks Wb' hWb'
        rw [Finset.preimage_map, Finset.preimage_map] at hne' ⊢
        have hWbne : U₀.map σ ≠ U₀'.map σ := fun h =>
          hne' (Finset.map_injective σ h)
        exact (Finset.disjoint_map σ).1 (hdisj hWb hWb' hWbne)
      · ext a
        rw [Finset.mem_sup]
        constructor
        · rintro ⟨U, hU, haU⟩
          obtain ⟨Wb, hWb, rfl⟩ := Finset.mem_image.1 hU
          obtain ⟨U₀, hU₀V, rfl⟩ := hblocks Wb hWb
          rw [Finset.preimage_map] at haU
          exact hU₀V haU
        · intro ha
          have : σ a ∈ Pa.sup id := by
            rw [hsup]
            exact Finset.mem_map_of_mem σ ha
          rw [Finset.mem_sup] at this
          obtain ⟨Wb, hWb, haWb⟩ := this
          obtain ⟨U₀, _, rfl⟩ := hblocks Wb hWb
          refine ⟨U₀, ?_, ?_⟩
          · rw [← Finset.preimage_map (f := σ) (s := U₀)]
            exact Finset.mem_image_of_mem _ hWb
          · have : a ∈ U₀ := by
              obtain ⟨a', ha', heq⟩ := Finset.mem_map.1 haWb
              rwa [← σ.injective heq]
            exact this
    · dsimp only
      rw [Finset.image_image]
      have : ∀ Wb ∈ Pa,
          ((fun W : Finset ι => W.map σ) ∘
            fun Wb' => Wb'.preimage σ σ.injective.injOn) Wb = Wb := by
        intro Wb hWb
        obtain ⟨U, _, rfl⟩ := hblocks Wb hWb
        simp only [Function.comp_apply, Finset.preimage_map]
      rw [Finset.image_congr fun Wb hWb => this Wb hWb]
      exact Finset.image_id
  · intro P _
    rfl

end Relabel

end PolymerKP
