/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Pphi2.ClusterExpansion.BKAR
import Pphi2.ClusterExpansion.EquivalenceMatrix

/-!
# Positive threshold matrices of a forest

At a fixed threshold, retain the forest edges whose interpolation parameter
is at least that threshold.  Connectivity in the retained graph is an
equivalence relation, so its zero-one component matrix is positive
semidefinite.
-/

namespace Pphi2.ClusterExpansion

/-- Forest edges open at level `r`. -/
def forestThresholdGraph
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ) :
    SimpleGraph Block :=
  SimpleGraph.fromRel fun i j => ∃ h : T.graph.Adj i j,
    r ≤ t ⟨s(i, j), T.graph.mem_edgeSet.mpr h⟩

theorem forestThresholdGraph_adj_iff
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ)
    (i j : Block) :
    (forestThresholdGraph T t r).Adj i j ↔
      ∃ h : T.graph.Adj i j,
        r ≤ t ⟨s(i, j), T.graph.mem_edgeSet.mpr h⟩ := by
  simp only [forestThresholdGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hij | hji⟩
    · exact hij
    · rcases hji with ⟨hji, ht⟩
      refine ⟨hji.symm, ?_⟩
      simpa only [Sym2.eq_swap] using ht
  · rintro ⟨hij, ht⟩
    refine ⟨?_, Or.inl ⟨hij, ht⟩⟩
    rintro rfl
    exact T.graph.loopless.irrefl _ hij

noncomputable instance forestThresholdGraph_adjDecidable
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ) :
    DecidableRel (forestThresholdGraph T t r).Adj :=
  Classical.decRel _

theorem forestThresholdGraph_le
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ) :
    forestThresholdGraph T t r ≤ T.graph := by
  intro i j hij
  rcases (forestThresholdGraph_adj_iff T t r i j).mp hij with ⟨hij, _⟩
  exact hij

theorem forestThresholdGraph_edge_mem_iff
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ)
    (e : ForestEdge T) :
    e.1 ∈ (forestThresholdGraph T t r).edgeSet ↔ r ≤ t e := by
  rcases e with ⟨e, he⟩
  induction e with
  | _ i j =>
      rw [(forestThresholdGraph T t r).mem_edgeSet]
      rw [forestThresholdGraph_adj_iff]
      change (∃ h : T.graph.Adj i j,
        r ≤ t ⟨s(i, j), T.graph.mem_edgeSet.mpr h⟩) ↔
          r ≤ t ⟨s(i, j), he⟩
      constructor
      · rintro ⟨_, hr⟩
        simpa using hr
      · intro hr
        exact ⟨T.graph.mem_edgeSet.mp he, by simpa using hr⟩

/-- Threshold connectivity is equivalent to every edge of the unique forest
path being open at that threshold. -/
theorem forestThresholdGraph_reachable_iff
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ)
    (i j : Block) (hreach : T.graph.Reachable i j) :
    (forestThresholdGraph T t r).Reachable i j ↔
      ∀ e ∈ forestPathEdges T i j, r ≤ t e := by
  classical
  let H := forestThresholdGraph T t r
  have hHT : H ≤ T.graph := forestThresholdGraph_le T t r
  constructor
  · intro hij
    obtain ⟨q, hq⟩ := hij.exists_isPath
    let qPath : H.Path i j := ⟨q, hq⟩
    let qPathT : T.graph.Path i j :=
      ⟨q.mapLe hHT, hq.mapLe hHT⟩
    have hpathEq : qPathT = chosenForestPath T i j hreach :=
      T.acyclic.path_unique _ _
    intro e he
    have heChosen :
        e.1 ∈ (chosenForestPath T i j hreach : T.graph.Walk i j).edges := by
      simpa [forestPathEdges, hreach] using he
    have heMapped : e.1 ∈ (q.mapLe hHT).edges := by
      have hwalkEq : q.mapLe hHT =
          (chosenForestPath T i j hreach : T.graph.Walk i j) := by
        simpa only [qPathT] using congrArg Subtype.val hpathEq
      rw [hwalkEq]
      exact heChosen
    have heQ : e.1 ∈ q.edges := by
      simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using heMapped
    have heH : e.1 ∈ H.edgeSet := q.edges_subset_edgeSet heQ
    exact (forestThresholdGraph_edge_mem_iff T t r e).mp heH
  · intro hall
    let p := chosenForestPath T i j hreach
    have hedge : ∀ e ∈ (p : T.graph.Walk i j).edges, e ∈ H.edgeSet := by
      intro e he
      have heT : e ∈ T.graph.edgeSet :=
        (p : T.graph.Walk i j).edges_subset_edgeSet he
      let edge : ForestEdge T := ⟨e, heT⟩
      have hedgePath : edge ∈ forestPathEdges T i j := by
        simp [forestPathEdges, hreach, edge, p, he]
      exact (forestThresholdGraph_edge_mem_iff T t r edge).mpr
        (hall edge hedgePath)
    exact ⟨(p : T.graph.Walk i j).transfer H hedge⟩

theorem forestThresholdGraph_reachable_iff_le_pathInf
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ)
    (i j : Block) (hreach : T.graph.Reachable i j)
    (hpath : (forestPathEdges T i j).Nonempty) :
    (forestThresholdGraph T t r).Reachable i j ↔
      r ≤ (forestPathEdges T i j).inf' hpath t := by
  rw [forestThresholdGraph_reachable_iff T t r i j hreach]
  constructor
  · intro hall
    exact Finset.le_inf' _ _ hall
  · intro hr e he
    exact hr.trans (Finset.inf'_le _ he)

theorem forestPathEdges_nonempty_of_reachable
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) (hij : i ≠ j)
    (hreach : T.graph.Reachable i j) :
    (forestPathEdges T i j).Nonempty := by
  classical
  let p := chosenForestPath T i j hreach
  have hedges : (p : T.graph.Walk i j).edges ≠ [] := by
    intro hempty
    exact hij ((SimpleGraph.Walk.edges_eq_nil.mp hempty).eq)
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hedges
  have heT : e ∈ T.graph.edgeSet :=
    (p : T.graph.Walk i j).edges_subset_edgeSet he
  exact ⟨⟨e, heT⟩, by simp [forestPathEdges, hreach, p, he]⟩

theorem forestPathEdges_nonempty_iff_reachable
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) (hij : i ≠ j) :
    (forestPathEdges T i j).Nonempty ↔ T.graph.Reachable i j := by
  constructor
  · intro hpath
    by_contra hreach
    simpa [forestPathEdges, hreach] using hpath
  · exact forestPathEdges_nonempty_of_reachable T i j hij

/-- Component matrix of the thresholded forest. -/
noncomputable def forestThresholdMatrix
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ) :
    Matrix Block Block ℝ :=
  relationMatrix (forestThresholdGraph T t r).Reachable

/-- Each threshold component matrix is positive semidefinite. -/
theorem forestThresholdMatrix_posSemidef
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) (r : ℝ) :
    (forestThresholdMatrix T t r).PosSemidef := by
  classical
  apply relationMatrix_posSemidef
  · exact fun i => SimpleGraph.Reachable.refl i
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ h₁ h₂ => h₁.trans h₂

/-- The finite set of threshold levels used by the forest.  The endpoints
`0` and `1` are included so the successive gaps telescope on the diagonal. -/
noncomputable def forestLevels
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) : Finset ℝ :=
  insert 0 (insert 1 (Finset.univ.image t))

theorem zero_mem_forestLevels
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    0 ∈ forestLevels T t := by
  simp [forestLevels]

theorem one_mem_forestLevels
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    1 ∈ forestLevels T t := by
  simp [forestLevels]

theorem forestLevels_nonempty
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    (forestLevels T t).Nonempty :=
  ⟨0, zero_mem_forestLevels T t⟩

theorem forestLevels_mem_Icc
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) {r : ℝ} (hr : r ∈ forestLevels T t) :
    r ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [forestLevels, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hr
  rcases hr with rfl | rfl | ⟨e, rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact unitCube_apply ht e

/-- Increasing enumeration of the distinct threshold levels. -/
noncomputable def forestLevel
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    Fin (forestLevels T t).card → ℝ :=
  fun k => ((forestLevels T t).orderIsoOfFin rfl k : ℝ)

theorem forestLevel_mem
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (k : Fin (forestLevels T t).card) :
    forestLevel T t k ∈ forestLevels T t :=
  ((forestLevels T t).orderIsoOfFin rfl k).2

/-- Successive gap preceding a threshold level. -/
noncomputable def forestLevelWeight
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (k : Fin (forestLevels T t).card) : ℝ :=
  let levelWithZero : Fin ((forestLevels T t).card + 1) → ℝ :=
    Fin.cases 0 (forestLevel T t)
  levelWithZero k.succ - levelWithZero k.castSucc

theorem forestLevelWeight_nonneg
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T)
    (k : Fin (forestLevels T t).card) :
    0 ≤ forestLevelWeight T t k := by
  classical
  by_cases hk : k.val = 0
  · have hlevel : 0 ≤ forestLevel T t k :=
      (forestLevels_mem_Icc T t ht (forestLevel_mem T t k)).1
    have hkzero : k.castSucc = 0 := Fin.ext hk
    simpa [forestLevelWeight, hkzero] using hlevel
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    let predecessor : Fin (forestLevels T t).card :=
      ⟨k - 1, (Nat.sub_one_lt hk).trans (Fin.is_lt k)⟩
    have hpred : predecessor < k := by
      exact Fin.mk_lt_mk.mpr (Nat.sub_one_lt hk)
    have hcast : k.castSucc = predecessor.succ := by
      apply Fin.ext
      simp [predecessor, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
    have hmono : forestLevel T t predecessor ≤ forestLevel T t k :=
      ((forestLevels T t).orderIsoOfFin rfl).monotone hpred.le
    simpa [forestLevelWeight, hcast] using sub_nonneg.mpr hmono

theorem sum_forestLevelWeight_Iic
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (q : Fin (forestLevels T t).card) :
    ∑ k ∈ Finset.Iic q, forestLevelWeight T t k = forestLevel T t q := by
  let levelWithZero : Fin ((forestLevels T t).card + 1) → ℝ :=
    Fin.cases 0 (forestLevel T t)
  have htel := Fin.sum_Iic_sub q levelWithZero
  simpa [forestLevelWeight, levelWithZero] using htel

theorem sum_forestLevelWeight
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) :
    ∑ k : Fin (forestLevels T t).card, forestLevelWeight T t k = 1 := by
  let E := (forestLevels T t).orderIsoOfFin rfl
  let q : Fin (forestLevels T t).card :=
    E.symm ⟨1, one_mem_forestLevels T t⟩
  have hIic : Finset.Iic q = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    rw [Finset.mem_Iic]
    apply E.le_symm_apply.mpr
    exact (forestLevels_mem_Icc T t ht (forestLevel_mem T t k)).2
  have hsum := sum_forestLevelWeight_Iic T t q
  rw [hIic] at hsum
  simpa [forestLevel, E, q] using hsum

theorem pathInf_mem_forestLevels
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) (hpath : (forestPathEdges T i j).Nonempty) :
    (forestPathEdges T i j).inf' hpath t ∈ forestLevels T t := by
  have hrange : (forestPathEdges T i j).inf' hpath t ∈ Set.range t :=
    Finset.inf'_mem (Set.range t) (fun x hx y hy => by
      rcases le_total x y with hxy | hyx
      · simpa [min_eq_left hxy] using hx
      · simpa [min_eq_right hyx] using hy)
      (forestPathEdges T i j) hpath t (fun e _ => ⟨e, rfl⟩)
  obtain ⟨e, he⟩ := hrange
  simp [forestLevels, ← he]

theorem forestThresholdGraph_reachable_at_level_iff
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) (hreach : T.graph.Reachable i j)
    (hpath : (forestPathEdges T i j).Nonempty)
    (k : Fin (forestLevels T t).card) :
    (forestThresholdGraph T t (forestLevel T t k)).Reachable i j ↔
      k ≤ ((forestLevels T t).orderIsoOfFin rfl).symm
        ⟨(forestPathEdges T i j).inf' hpath t,
          pathInf_mem_forestLevels T t i j hpath⟩ := by
  rw [forestThresholdGraph_reachable_iff_le_pathInf
    T t (forestLevel T t k) i j hreach hpath]
  let E := (forestLevels T t).orderIsoOfFin rfl
  have hle := E.le_symm_apply
    (x := k)
    (y := ⟨(forestPathEdges T i j).inf' hpath t,
      pathInf_mem_forestLevels T t i j hpath⟩)
  exact hle.symm

/-- The path-min coupling matrix is the finite sum of threshold-component
matrices weighted by successive threshold gaps. -/
theorem forestEdgeCouplingMatrix_eq_threshold_sum
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) :
    edgeCouplingMatrix (forestEdgePoint T t) =
      ∑ k : Fin (forestLevels T t).card,
        forestLevelWeight T t k •
          forestThresholdMatrix T t (forestLevel T t k) := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    have hdiag : ∀ k : Fin (forestLevels T t).card,
        forestThresholdMatrix T t (forestLevel T t k) i i = 1 := by
      intro k
      simp [forestThresholdMatrix, relationMatrix]
    simp_rw [hdiag, mul_one]
    simp [edgeCouplingMatrix, sum_forestLevelWeight T t ht]
  · by_cases hreach : T.graph.Reachable i j
    · have hpath : (forestPathEdges T i j).Nonempty :=
        forestPathEdges_nonempty_of_reachable T i j hij hreach
      let q : Fin (forestLevels T t).card :=
        ((forestLevels T t).orderIsoOfFin rfl).symm
          ⟨(forestPathEdges T i j).inf' hpath t,
            pathInf_mem_forestLevels T t i j hpath⟩
      have hentry : ∀ k : Fin (forestLevels T t).card,
          forestThresholdMatrix T t (forestLevel T t k) i j =
            if k ≤ q then 1 else 0 := by
        intro k
        simp only [forestThresholdMatrix, relationMatrix]
        rw [if_congr
          (forestThresholdGraph_reachable_at_level_iff
            T t i j hreach hpath k) rfl rfl]
      simp_rw [hentry]
      have hfiltered :
          (∑ k : Fin (forestLevels T t).card,
            if k ≤ q then forestLevelWeight T t k else 0) =
            ∑ k ∈ Finset.Iic q, forestLevelWeight T t k := by
        rw [← Finset.sum_filter, Finset.filter_ge_eq_Iic]
      rw [show (∑ k : Fin (forestLevels T t).card,
          forestLevelWeight T t k * if k ≤ q then 1 else 0) =
          ∑ k ∈ Finset.Iic q, forestLevelWeight T t k by
            simpa only [mul_ite, mul_one, mul_zero] using hfiltered]
      rw [sum_forestLevelWeight_Iic]
      simp [edgeCouplingMatrix, hij, forestEdgePoint_eq_pathInf,
        hpath, q, forestLevel]
    · have hthreshold : ∀ k : Fin (forestLevels T t).card,
          ¬(forestThresholdGraph T t (forestLevel T t k)).Reachable i j := by
        intro k hk
        exact hreach (hk.mono (forestThresholdGraph_le T t (forestLevel T t k)))
      have hpath : forestPathEdges T i j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hp
        exact hreach ((forestPathEdges_nonempty_iff_reachable T i j hij).mp hp)
      simp [forestThresholdMatrix, relationMatrix, hthreshold,
        edgeCouplingMatrix, hij,
        forestEdgePoint_eq_zero_of_disconnected T t i j hij hpath]

/-- A finite threshold decomposition of the path-min coupling matrix.  The
weights are the successive gaps between distinct edge levels. -/
structure ForestThresholdDecomposition
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) where
  levelCount : ℕ
  level : Fin levelCount → ℝ
  weight : Fin levelCount → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  matrix_eq :
    edgeCouplingMatrix (forestEdgePoint T t) =
      ∑ k : Fin levelCount, weight k • forestThresholdMatrix T t (level k)

/-- A threshold decomposition proves the path-min coupling matrix is PSD. -/
theorem forestEdgeCouplingMatrix_posSemidef_of_decomposition
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (D : ForestThresholdDecomposition T t) :
    (edgeCouplingMatrix (forestEdgePoint T t)).PosSemidef := by
  rw [D.matrix_eq]
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  exact (forestThresholdMatrix_posSemidef T t (D.level k)).smul
    (D.weight_nonneg k)

/-- The canonical finite threshold decomposition of every forest point in
the edge cube. -/
noncomputable def forestThresholdDecomposition
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) : ForestThresholdDecomposition T t where
  levelCount := (forestLevels T t).card
  level := forestLevel T t
  weight := forestLevelWeight T t
  weight_nonneg := forestLevelWeight_nonneg T t ht
  matrix_eq := forestEdgeCouplingMatrix_eq_threshold_sum T t ht

/-- Every forest path-min coupling matrix in the unit cube is positive
semidefinite. -/
theorem forestEdgeCouplingMatrix_posSemidef
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) :
    (edgeCouplingMatrix (forestEdgePoint T t)).PosSemidef :=
  forestEdgeCouplingMatrix_posSemidef_of_decomposition T t
    (forestThresholdDecomposition T t ht)

end Pphi2.ClusterExpansion
