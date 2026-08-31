/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Order.Lattice

/-!
# Finite BKAR forest data

This file supplies the finite forest, edge-cube, path interpolation, and
directional-derivative objects used by the Abdesselam--Rivasseau formula.
The one-edge formula is the fundamental-theorem-of-calculus base case of the
finite forest identity.
-/

open MeasureTheory Set
open scoped BigOperators ContDiff Interval

namespace Pphi2.ClusterExpansion

/-- Unordered pairs of physical blocks. -/
abbrev BlockEdge (Block : Type*) := Sym2 Block

/-- A spanning forest on a finite block set.  Isolated blocks are retained. -/
structure SpanningForest (Block : Type*) [Fintype Block] where
  graph : SimpleGraph Block
  acyclic : graph.IsAcyclic

/-- Edges belonging to a spanning forest. -/
abbrev ForestEdge {Block : Type*} [Fintype Block]
    (T : SpanningForest Block) :=
  {e : Sym2 Block // e ∈ T.graph.edgeSet}

noncomputable instance forestEdgeFintype
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) : Fintype (ForestEdge T) :=
  Fintype.ofFinite _

noncomputable instance spanningForestFintype
    {Block : Type*} [Fintype Block] [DecidableEq Block] :
    Fintype (SpanningForest Block) :=
  Fintype.ofInjective SpanningForest.graph fun T U h => by
    cases T
    cases U
    simp_all

/-- The parameter cube carried by the edges of a forest. -/
def unitCube {Block : Type*} [Fintype Block]
    (T : SpanningForest Block) : Set (ForestEdge T → ℝ) :=
  Set.Icc 0 1

/-- Product Lebesgue measure on the closed unit edge cube. -/
noncomputable def unitCubeMeasure
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) : Measure (ForestEdge T → ℝ) :=
  Measure.pi (fun _ : ForestEdge T =>
    Measure.restrict volume (Set.Icc (0 : ℝ) 1))

theorem unitCubeMeasure_eq_product
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) :
    unitCubeMeasure T =
      Measure.pi (fun _ : ForestEdge T =>
        Measure.restrict volume (Set.Icc (0 : ℝ) 1)) :=
  rfl

theorem unitCube_apply
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    {T : SpanningForest Block} {t : ForestEdge T → ℝ}
    (ht : t ∈ unitCube T) (e : ForestEdge T) :
    t e ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ht.1 e, ht.2 e⟩

/-- A chosen simple path in a reachable forest component. -/
noncomputable def chosenForestPath
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block)
    (h : T.graph.Reachable i j) : T.graph.Path i j :=
  ⟨Classical.choose h.exists_isPath,
    Classical.choose_spec h.exists_isPath⟩

/-- Edges of the unique simple forest path.  The choice used to construct the
path disappears extensionally because an acyclic graph has at most one path
between fixed endpoints. -/
noncomputable def forestPathEdges
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) : Finset (ForestEdge T) := by
  classical
  exact if h : T.graph.Reachable i j then
    Finset.univ.filter fun e : ForestEdge T =>
      e.1 ∈ (chosenForestPath T i j h : T.graph.Walk i j).edges
  else ∅

theorem forestPathEdges_comm
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) :
    forestPathEdges T i j = forestPathEdges T j i := by
  classical
  by_cases h : T.graph.Reachable i j
  · have hrev : T.graph.Reachable j i := h.symm
    have hpath : chosenForestPath T j i hrev =
        (chosenForestPath T i j h).reverse :=
      T.acyclic.path_unique _ _
    simp [forestPathEdges, h, hrev, hpath]
  · have hrev : ¬T.graph.Reachable j i := fun hji => h hji.symm
    simp [forestPathEdges, h, hrev]

/-- The path-minimum coupling of two vertices, with zero between distinct
components and one on the diagonal. -/
noncomputable def forestPairCoupling
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) : ℝ :=
  if hij : i = j then 1
  else if hpath : (forestPathEdges T i j).Nonempty then
    (forestPathEdges T i j).inf' hpath t
  else 0

theorem forestPairCoupling_comm
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) :
    forestPairCoupling T t i j = forestPairCoupling T t j i := by
  classical
  rw [forestPairCoupling, forestPairCoupling, forestPathEdges_comm T i j]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem forestPairCoupling_mem_Icc
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (ht : t ∈ unitCube T) (i j : Block) :
    forestPairCoupling T t i j ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hij : i = j
  · simp [forestPairCoupling, hij]
  · by_cases hpath : (forestPathEdges T i j).Nonempty
    · rw [forestPairCoupling, dif_neg hij, dif_pos hpath]
      constructor
      · exact Finset.le_inf' _ _ fun e _ => (unitCube_apply ht e).1
      · obtain ⟨e, he⟩ := hpath
        exact (Finset.inf'_le _ he).trans (unitCube_apply ht e).2
    · simp [forestPairCoupling, hij, hpath]

theorem forestPairCoupling_continuous
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) :
    Continuous (fun t : ForestEdge T → ℝ =>
      forestPairCoupling T t i j) := by
  classical
  by_cases hij : i = j
  · simpa only [forestPairCoupling, dif_pos hij] using
      (continuous_const : Continuous
        (fun _ : ForestEdge T → ℝ => (1 : ℝ)))
  · by_cases hpath : (forestPathEdges T i j).Nonempty
    · simp only [forestPairCoupling, dif_neg hij, dif_pos hpath]
      exact Continuous.finset_inf'_apply hpath fun e _ => continuous_apply e
    · simpa only [forestPairCoupling, dif_neg hij, dif_neg hpath] using
        (continuous_const : Continuous
          (fun _ : ForestEdge T → ℝ => (0 : ℝ)))

/-- The BKAR point in the complete edge-parameter space. -/
noncomputable def forestEdgePoint
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    BlockEdge Block → ℝ :=
  Sym2.lift
    ⟨forestPairCoupling T t, forestPairCoupling_comm T t⟩

theorem forestEdgePoint_eval_continuous
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block) :
    Continuous (fun t : ForestEdge T → ℝ => forestEdgePoint T t e) := by
  induction e using Sym2.inductionOn with
  | _ i j => exact forestPairCoupling_continuous T i j

theorem forestEdgePoint_continuous
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) :
    Continuous (forestEdgePoint T) :=
  continuous_pi fun e => forestEdgePoint_eval_continuous T e

theorem forestEdgePoint_eq_pathInf
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) (hij : i ≠ j)
    (hpath : (forestPathEdges T i j).Nonempty) :
    forestEdgePoint T t s(i, j) =
      (forestPathEdges T i j).inf' hpath t := by
  simp [forestEdgePoint, forestPairCoupling, hij, hpath]

theorem forestEdgePoint_eq_zero_of_disconnected
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (t : ForestEdge T → ℝ)
    (i j : Block) (hij : i ≠ j)
    (hpath : forestPathEdges T i j = ∅) :
    forestEdgePoint T t s(i, j) = 0 := by
  simp [forestEdgePoint, forestPairCoupling, hij, hpath]

/-- Turn edge parameters into a symmetric block-coupling matrix. -/
def edgeCouplingMatrix
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (u : BlockEdge Block → ℝ) : Matrix Block Block ℝ :=
  fun i j => if i = j then 1 else u s(i, j)

/-- Coordinate direction associated with one unordered block edge. -/
def edgeBasis {Block : Type*} [DecidableEq (BlockEdge Block)]
    (e : BlockEdge Block) : BlockEdge Block → ℝ :=
  fun e' => if e' = e then 1 else 0

/-- An unordered block pair whose endpoints lie in distinct components of a
forest.  Diagonal pairs are excluded because reachability is reflexive. -/
noncomputable def forestSeparated
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) : BlockEdge Block → Prop :=
  Sym2.lift ⟨fun i j => ¬T.graph.Reachable i j, by
    intro i j
    apply propext
    exact ⟨fun hij hji => hij hji.symm, fun hji hij => hji hij.symm⟩⟩

@[simp]
theorem forestSeparated_mk
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (i j : Block) :
    forestSeparated T s(i, j) ↔ ¬T.graph.Reachable i j :=
  Iff.rfl

/-- Adjoining an edge between distinct forest components preserves
acyclicity. -/
noncomputable def SpanningForest.addSeparatedEdge
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block)
    (he : forestSeparated T e) : SpanningForest Block := by
  let G := T.graph ⊔ SimpleGraph.fromEdgeSet ({e} : Set (BlockEdge Block))
  have hacyclic : G.IsAcyclic := by
    induction e using Sym2.inductionOn with
    | _ i j =>
        simpa only [G, SimpleGraph.edge] using
          T.acyclic.sup_edge_of_not_reachable
            ((forestSeparated_mk T i j).mp he)
  exact ⟨G, hacyclic⟩

@[simp]
theorem SpanningForest.addSeparatedEdge_graph
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block)
    (he : forestSeparated T e) :
    (T.addSeparatedEdge e he).graph =
      T.graph ⊔ SimpleGraph.fromEdgeSet ({e} : Set (BlockEdge Block)) := by
  rfl

theorem forestSeparated_of_addSeparatedEdge
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e f : BlockEdge Block)
    (he : forestSeparated T e)
    (hf : forestSeparated (T.addSeparatedEdge e he) f) :
    forestSeparated T f := by
  induction f using Sym2.inductionOn with
  | _ i j =>
      rw [forestSeparated_mk] at hf ⊢
      intro hij
      apply hf
      apply hij.mono
      rw [T.addSeparatedEdge_graph e he]
      exact le_sup_left

theorem not_forestSeparated_addSeparatedEdge_self
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block)
    (he : forestSeparated T e) :
    ¬forestSeparated (T.addSeparatedEdge e he) e := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      rw [forestSeparated_mk]
      push_neg
      have hij : i ≠ j := by
        intro h
        subst j
        exact he (SimpleGraph.Reachable.refl i)
      apply SimpleGraph.Adj.reachable
      rw [T.addSeparatedEdge_graph s(i, j) he]
      exact Or.inr (by simp [SimpleGraph.fromEdgeSet_adj, hij])

/-- Complete-graph edges joining distinct components of a forest. -/
noncomputable def forestConnectingEdges
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) : Finset (BlockEdge Block) := by
  classical
  exact Finset.univ.filter (forestSeparated T)

@[simp]
theorem mem_forestConnectingEdges
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block) :
    e ∈ forestConnectingEdges T ↔ forestSeparated T e := by
  classical
  simp [forestConnectingEdges]

theorem forestConnectingEdges_card_addSeparatedEdge_lt
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) (e : BlockEdge Block)
    (he : forestSeparated T e) :
    (forestConnectingEdges (T.addSeparatedEdge e he)).card <
      (forestConnectingEdges T).card := by
  classical
  apply Finset.card_lt_card
  have hsubset : forestConnectingEdges (T.addSeparatedEdge e he) ⊆
      forestConnectingEdges T := by
    intro f hf
    rw [mem_forestConnectingEdges] at hf ⊢
    exact forestSeparated_of_addSeparatedEdge T e f he hf
  rw [Finset.ssubset_iff_of_subset hsubset]
  exact ⟨e, (mem_forestConnectingEdges T e).mpr he,
    fun hmem => not_forestSeparated_addSeparatedEdge_self T e he
      ((mem_forestConnectingEdges _ e).mp hmem)⟩

/-- Direction that raises all couplings between distinct forest components
at the same rate. -/
noncomputable def forestComponentDirection
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (T : SpanningForest Block) : BlockEdge Block → ℝ := by
  classical
  exact fun e => if forestSeparated T e then 1 else 0

/-- The component direction is the sum of the coordinate directions of the
currently admissible forest edges. -/
theorem forestComponentDirection_eq_sum_edgeBasis
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)] (T : SpanningForest Block) :
    forestComponentDirection T =
      ∑ e ∈ forestConnectingEdges T, edgeBasis e := by
  classical
  funext e'
  by_cases hsep : forestSeparated T e'
  · simp [forestComponentDirection, forestConnectingEdges, edgeBasis, hsep]
  · simp [forestComponentDirection, forestConnectingEdges, edgeBasis, hsep]

/-- Differentiating in the component direction is the finite sum of the
coordinate derivatives over edges that join distinct components. -/
theorem fderiv_forestComponentDirection_eq_sum
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (x : BlockEdge Block → ℝ)
    (T : SpanningForest Block) :
    fderiv ℝ F x (forestComponentDirection T) =
      ∑ e ∈ forestConnectingEdges T, fderiv ℝ F x (edgeBasis e) := by
  rw [forestComponentDirection_eq_sum_edgeBasis T]
  simp only [map_sum]

/-- Repeated Fréchet directional derivative in the listed directions. -/
noncomputable def iteratedDirectionalDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) : List E → E → ℝ
  | [], x => F x
  | direction :: directions, x =>
      fderiv ℝ (iteratedDirectionalDerivative F directions) x direction

theorem iteratedDirectionalDerivative_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (directions : List E) :
    ContDiff ℝ ∞ (iteratedDirectionalDerivative F directions) := by
  induction directions with
  | nil => simpa [iteratedDirectionalDerivative] using hF
  | cons direction directions ih =>
      have hderiv : ContDiff ℝ ∞
          (fderiv ℝ (iteratedDirectionalDerivative F directions)) :=
        (contDiff_infty_iff_fderiv.mp ih).2
      simpa [iteratedDirectionalDerivative] using
        hderiv.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => direction))

/-- Forest derivative with one complete-edge direction for each forest edge. -/
noncomputable def forestDerivative
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ)
    (T : SpanningForest Block) : (BlockEdge Block → ℝ) → ℝ :=
  iteratedDirectionalDerivative F
    ((Finset.univ : Finset (ForestEdge T)).toList.map
      (fun e => edgeBasis e.1))

theorem forestDerivative_contDiff
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (T : SpanningForest Block) :
    ContDiff ℝ ∞ (forestDerivative F T) :=
  iteratedDirectionalDerivative_contDiff F hF _

theorem forestDerivative_forestEdgePoint_continuous
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (T : SpanningForest Block) :
    Continuous (fun t => forestDerivative F T (forestEdgePoint T t)) :=
  (forestDerivative_contDiff F hF T).continuous.comp
    (forestEdgePoint_continuous T)

/-- The fully coupled point in complete edge-coordinate space. -/
def completeEdgePoint {Block : Type*} : BlockEdge Block → ℝ :=
  fun _ => 1

/-- Contribution of one spanning forest to the BKAR sum. -/
noncomputable def bkarForestTerm
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (T : SpanningForest Block) : ℝ :=
  ∫ t, forestDerivative F T (forestEdgePoint T t) ∂unitCubeMeasure T

/-- The finite Abdesselam--Rivasseau forest sum. -/
noncomputable def bkarForestSum
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) : ℝ :=
  ∑ T : SpanningForest Block, bkarForestTerm F T

/-- The unordered cube packaging of the finite BKAR formula.  The proved
identity below uses the equivalent ordered Abdesselam--Rivasseau recursion. -/
def CubeBKARIdentity
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) : Prop :=
  F completeEdgePoint = bkarForestSum F

/-- The one-edge Abdesselam--Rivasseau identity.  This is the two-block
instance of the finite forest formula. -/
theorem bkar_one_edge_identity (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    F 1 = F 0 + ∫ t in (0 : ℝ)..1, deriv F t := by
  have hdifferentiable : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ F t := fun t _ =>
    (hF.differentiable (by norm_num)).differentiableAt
  have hintegrable : IntervalIntegrable (deriv F) volume 0 1 :=
    (hF.continuous_deriv (by norm_num)).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_deriv_eq_sub
    hdifferentiable hintegrable
  linarith

theorem deriv_comp_add_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {x v : E} {t : ℝ}
    (hF : DifferentiableAt ℝ F (x + t • v)) :
    deriv (fun s : ℝ => F (x + s • v)) t =
      fderiv ℝ F (x + t • v) v := by
  have hpath : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hF.hasFDerivAt.comp_hasDerivAt t hpath).deriv

/-- Fundamental theorem of calculus along an affine line in the complete
edge-coordinate space.  This is the local step iterated by the finite AR
forest recursion. -/
theorem bkar_directional_fundamental
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (x v : E) :
    F (x + v) = F x +
      ∫ s in (0 : ℝ)..1, fderiv ℝ F (x + s • v) v := by
  let g : ℝ → ℝ := fun s => F (x + s • v)
  have hg : ContDiff ℝ 1 g := by
    have hx : ContDiff ℝ 1 (fun _ : ℝ => x) := contDiff_const
    have hid : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
    have hv : ContDiff ℝ 1 (fun s : ℝ => s • v) :=
      ContDiff.smul_const hid v
    apply (hF.of_le (by simp)).comp
    exact ContDiff.add hx hv
  have hderiv : ∀ s : ℝ,
      deriv g s = fderiv ℝ F (x + s • v) v := by
    intro s
    exact deriv_comp_add_smul
      (hF.differentiable (by simp)).differentiableAt
  have hftc := bkar_one_edge_identity g hg
  simp_rw [hderiv] at hftc
  simpa [g] using hftc

/-- Affine-line FTC with a variable upper endpoint. -/
theorem bkar_directional_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (x v : E) (u : ℝ) :
    F (x + u • v) = F x +
      ∫ s in (0 : ℝ)..u, fderiv ℝ F (x + s • v) v := by
  let g : ℝ → ℝ := fun s => F (x + s • v)
  have hderiv : ∀ s : ℝ,
      deriv g s = fderiv ℝ F (x + s • v) v := by
    intro s
    exact deriv_comp_add_smul
      (hF.differentiable (by simp)).differentiableAt
  have hdifferentiable : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) u →
      DifferentiableAt ℝ g s := by
    intro s _
    exact (hF.differentiable (by simp)).differentiableAt.comp s
      ((hasDerivAt_id s).smul_const v |>.const_add x).differentiableAt
  have hintegrable : IntervalIntegrable (deriv g) volume 0 u := by
    have hg : ContDiff ℝ 1 g := by
      have hx : ContDiff ℝ 1 (fun _ : ℝ => x) := contDiff_const
      have hid : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
      have hv : ContDiff ℝ 1 (fun s : ℝ => s • v) :=
        ContDiff.smul_const hid v
      apply (hF.of_le (by simp)).comp
      exact ContDiff.add hx hv
    exact (hg.continuous_deriv (by norm_num)).intervalIntegrable 0 u
  have hftc := intervalIntegral.integral_deriv_eq_sub
    hdifferentiable hintegrable
  simp_rw [hderiv] at hftc
  dsimp [g] at hftc
  simp only [zero_smul, add_zero] at hftc
  linarith

/-- Variable-endpoint form of one AR recursion step. -/
theorem bkar_component_interval
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : BlockEdge Block → ℝ) (T : SpanningForest Block) (u : ℝ) :
    F (x + u • forestComponentDirection T) = F x +
      ∑ e ∈ forestConnectingEdges T,
        ∫ s in (0 : ℝ)..u,
          fderiv ℝ F (x + s • forestComponentDirection T) (edgeBasis e) := by
  have hftc := bkar_directional_interval F hF x
    (forestComponentDirection T) u
  have hint : ∀ e ∈ forestConnectingEdges T,
      IntervalIntegrable
        (fun s : ℝ =>
          fderiv ℝ F (x + s • forestComponentDirection T) (edgeBasis e))
        volume 0 u := by
    intro e _
    apply Continuous.intervalIntegrable
    have hid : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
    have hdir : ContDiff ℝ 1
        (fun s : ℝ => s • forestComponentDirection T) :=
      ContDiff.smul_const hid (forestComponentDirection T)
    have hpath : Continuous
        (fun s : ℝ => x + s • forestComponentDirection T) :=
      (ContDiff.add (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x))
        hdir).continuous
    have hp : Continuous (fun s : ℝ =>
        (x + s • forestComponentDirection T, edgeBasis e)) :=
      hpath.prodMk continuous_const
    convert (hF.continuous_fderiv_apply (by simp)).comp hp using 1
    rfl
  simp_rw [fderiv_forestComponentDirection_eq_sum F _ T] at hftc
  rw [intervalIntegral.integral_finsetSum hint] at hftc
  exact hftc

/-- The ordered Abdesselam--Rivasseau expansion obtained by recursively
joining distinct forest components.  The next edge parameter is integrated
only up to the preceding parameter. -/
noncomputable def orderedARExpansion
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (T : SpanningForest Block)
    (F : (BlockEdge Block → ℝ) → ℝ)
    (x : BlockEdge Block → ℝ) (u : ℝ) : ℝ :=
  F x + ∑ eh ∈ (forestConnectingEdges T).attach,
    ∫ s in (0 : ℝ)..u,
      orderedARExpansion
        (T.addSeparatedEdge eh.1
          ((mem_forestConnectingEdges T eh.1).mp eh.2))
        (fun y => fderiv ℝ F y (edgeBasis eh.1))
        (x + s • (forestComponentDirection T -
          forestComponentDirection
            (T.addSeparatedEdge eh.1
              ((mem_forestConnectingEdges T eh.1).mp eh.2)))) s
termination_by (forestConnectingEdges T).card
decreasing_by
  exact forestConnectingEdges_card_addSeparatedEdge_lt T eh.1
    ((mem_forestConnectingEdges T eh.1).mp eh.2)

/-- The finite ordered AR recursion evaluates the smooth function at the
point obtained by fully coupling the current forest components. -/
theorem orderedARExpansion_eq
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (T : SpanningForest Block)
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : BlockEdge Block → ℝ) (u : ℝ) :
    orderedARExpansion T F x u =
      F (x + u • forestComponentDirection T) := by
  induction hn : (forestConnectingEdges T).card using Nat.strong_induction_on
      generalizing T F x u with
  | h n ih =>
      rw [orderedARExpansion]
      rw [bkar_component_interval F hF x T u]
      congr 1
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro eh _
      apply intervalIntegral.integral_congr
      intro s _
      have he : forestSeparated T eh.1 :=
        (mem_forestConnectingEdges T eh.1).mp eh.2
      have hcard := forestConnectingEdges_card_addSeparatedEdge_lt T eh.1 he
      have hderiv : ContDiff ℝ ∞
          (fun y => fderiv ℝ F y (edgeBasis eh.1)) := by
        have hfderiv : ContDiff ℝ ∞ (fderiv ℝ F) :=
          (contDiff_infty_iff_fderiv.mp hF).2
        exact hfderiv.clm_apply
          (contDiff_const : ContDiff ℝ ∞
            (fun _ : BlockEdge Block → ℝ => edgeBasis eh.1))
      have hrec := ih _ (hn ▸ hcard)
        (T.addSeparatedEdge eh.1 he)
        (fun y => fderiv ℝ F y (edgeBasis eh.1)) hderiv
        (x + s • (forestComponentDirection T -
          forestComponentDirection (T.addSeparatedEdge eh.1 he))) s rfl
      simpa only [Pi.sub_apply, smul_sub, add_assoc, sub_add_cancel] using hrec

/-- The forest with all vertices isolated. -/
def emptySpanningForest (Block : Type*) [Fintype Block] :
    SpanningForest Block where
  graph := ⊥
  acyclic := by simp

/-- Complete-edge coordinates at the decoupled point: one on diagonal pairs
and zero on distinct pairs. -/
noncomputable def diagonalEdgePoint
    {Block : Type*} [DecidableEq Block] : BlockEdge Block → ℝ :=
  Sym2.lift ⟨fun i j => if i = j then 1 else 0, by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]⟩

theorem diagonalEdgePoint_add_emptyComponentDirection
    {Block : Type*} [Fintype Block] [DecidableEq Block] :
    diagonalEdgePoint +
        forestComponentDirection (emptySpanningForest Block) =
      completeEdgePoint := by
  classical
  funext e
  induction e using Sym2.inductionOn with
  | _ i j =>
      by_cases hij : i = j
      · subst j
        simp [diagonalEdgePoint, forestComponentDirection, forestSeparated,
          emptySpanningForest, completeEdgePoint]
      · simp [diagonalEdgePoint, forestComponentDirection, forestSeparated,
          emptySpanningForest, completeEdgePoint, hij]

/-- Full finite ordered Abdesselam--Rivasseau forest identity.  Repeated
integrals have decreasing upper endpoints and every recursive branch adds an
acyclic edge between two current components. -/
theorem ar_forest_identity
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    F completeEdgePoint =
      orderedARExpansion (emptySpanningForest Block) F diagonalEdgePoint 1 := by
  rw [orderedARExpansion_eq (emptySpanningForest Block) F hF diagonalEdgePoint 1]
  rw [one_smul, diagonalEdgePoint_add_emptyComponentDirection]

/-- One AR recursion step.  Raising every coupling between distinct
components decomposes into the sum of the admissible edge derivatives. -/
theorem bkar_component_fundamental
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    [DecidableEq (BlockEdge Block)]
    (F : (BlockEdge Block → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : BlockEdge Block → ℝ) (T : SpanningForest Block) :
    F (x + forestComponentDirection T) = F x +
      ∑ e ∈ forestConnectingEdges T,
        ∫ s in (0 : ℝ)..1,
          fderiv ℝ F (x + s • forestComponentDirection T) (edgeBasis e) := by
  have hftc := bkar_directional_fundamental F hF x
    (forestComponentDirection T)
  have hint : ∀ e ∈ forestConnectingEdges T,
      IntervalIntegrable
        (fun s : ℝ =>
          fderiv ℝ F (x + s • forestComponentDirection T) (edgeBasis e))
        volume 0 1 := by
    intro e _
    apply Continuous.intervalIntegrable
    have hid : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
    have hdir : ContDiff ℝ 1
        (fun s : ℝ => s • forestComponentDirection T) :=
      ContDiff.smul_const hid (forestComponentDirection T)
    have hpath : Continuous
        (fun s : ℝ => x + s • forestComponentDirection T) :=
      (ContDiff.add (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x))
        hdir).continuous
    have hp : Continuous (fun s : ℝ =>
        (x + s • forestComponentDirection T, edgeBasis e)) :=
      hpath.prodMk continuous_const
    convert (hF.continuous_fderiv_apply (by simp)).comp hp using 1
    rfl
  simp_rw [fderiv_forestComponentDirection_eq_sum F _ T] at hftc
  rw [intervalIntegral.integral_finsetSum hint] at hftc
  exact hftc

end Pphi2.ClusterExpansion
