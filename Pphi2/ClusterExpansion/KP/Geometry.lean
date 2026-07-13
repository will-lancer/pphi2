/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/Geometry.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Pphi2.ClusterExpansion.KP.Overlap

/-! # Lattice geometry for the finite-range tail bound -/

open scoped BigOperators

namespace PolymerKP

set_option linter.unusedSectionVars false

/-! ## Inlined from GibbsMeasure `Ch6Subtree/Foundations/Lattice.lean`

The upstream file imports `Ch6Subtree.Foundations.Lattice` only for the three
declarations below (`Zd`, `Region`, `zdL1Dist`), copied verbatim here so that
this mirror stays Mathlib-only. -/

/-- The `d`-dimensional integer lattice `ℤ^d`. -/
abbrev Zd (d : Nat) := Fin d -> Int

/-- A finite region of sites. -/
abbrev Region (Site : Type*) := Finset Site

/-- The `ℓ¹` distance on `Zd d`. -/
def zdL1Dist {d : Nat} (x y : Zd d) : Nat :=
  ∑ k : Fin d, Int.natAbs (x k - y k)

variable {d : ℕ}

/-! ## Basic facts about the `ℓ¹` distance on `Zd d` -/

theorem zdL1Dist_self (x : Zd d) : zdL1Dist x x = 0 := by
  unfold zdL1Dist
  simp

theorem zdL1Dist_symm (x y : Zd d) : zdL1Dist x y = zdL1Dist y x := by
  unfold zdL1Dist
  exact Finset.sum_congr rfl fun k _ => by omega

theorem zdL1Dist_triangle (x y z : Zd d) :
    zdL1Dist x z ≤ zdL1Dist x y + zdL1Dist y z := by
  unfold zdL1Dist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h : x k - z k = (x k - y k) + (y k - z k) := by ring
  rw [h]
  exact Int.natAbs_add_le _ _

/-! ## Step-connectivity within a finite set of lattice points -/

/-- One `R`-bounded step within the finite set `U`. -/
def StepIn (U : Finset (Zd d)) (R : ℕ) (u v : Zd d) : Prop :=
  u ∈ U ∧ v ∈ U ∧ zdL1Dist u v ≤ R

/-- `R`-step connectivity of a finite set of lattice points. -/
def StepConn (U : Finset (Zd d)) (R : ℕ) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (StepIn U R) u v

/-! ## The main diameter bound for step-connected sets

The layer-growth argument: the ball layers `layer x U R k` around a fixed point
`x ∈ U` grow strictly (in cardinality) at each radius increment of `R` until
they exhaust `U`, so `U` is exhausted after at most `U.card - 1` increments. -/

/-- The `k`-th layer around `x` inside `U`: points of `U` at distance at most
`k * R` from `x`. -/
private def layer (x : Zd d) (U : Finset (Zd d)) (R k : ℕ) : Finset (Zd d) :=
  U.filter (fun u => zdL1Dist x u ≤ k * R)

private theorem mem_layer {x : Zd d} {U : Finset (Zd d)} {R k : ℕ} {u : Zd d} :
    u ∈ layer x U R k ↔ u ∈ U ∧ zdL1Dist x u ≤ k * R :=
  Finset.mem_filter

/-- **Diameter bound for step-connected finite sets.** If `U` is `R`-step
connected, then any two of its points lie within `ℓ¹` distance `R * (U.card - 1)`
of each other. -/
theorem card_ge_of_stepConn {U : Finset (Zd d)} {R : ℕ}
    (hconn : StepConn U R) {x y : Zd d} (hx : x ∈ U) (hy : y ∈ U) :
    zdL1Dist x y ≤ R * (U.card - 1) := by
  have hLsub : ∀ k, layer x U R k ⊆ U := fun _k => Finset.filter_subset _ _
  have hxL : ∀ k, x ∈ layer x U R k := fun k =>
    mem_layer.mpr ⟨hx, by simp [zdL1Dist_self]⟩
  have hmono : ∀ k, layer x U R k ⊆ layer x U R (k + 1) := by
    intro k u hu
    obtain ⟨huU, hdist⟩ := mem_layer.mp hu
    exact mem_layer.mpr ⟨huU, hdist.trans (Nat.mul_le_mul (Nat.le_succ k) le_rfl)⟩
  -- Key growth step: as long as the layer is not all of `U`, it grows strictly.
  have hgrow : ∀ k, layer x U R k ≠ U →
      (layer x U R k).card < (layer x U R (k + 1)).card := by
    intro k hne
    apply Finset.card_lt_card
    rw [Finset.ssubset_def]
    refine ⟨hmono k, fun hsub => hne ?_⟩
    -- if the next layer were contained in this one, membership in the layer
    -- would be closed under `StepIn U R` steps, hence contain everything
    -- reachable from `x`, hence all of `U` by connectivity.
    have hclosed : ∀ u, Relation.ReflTransGen (StepIn U R) x u →
        u ∈ layer x U R k := by
      intro u hreach
      induction hreach with
      | refl => exact hxL k
      | @tail w v _hxw hstep ih =>
        refine hsub (mem_layer.mpr ⟨hstep.2.1, ?_⟩)
        have hwd : zdL1Dist x w ≤ k * R := (mem_layer.mp ih).2
        calc zdL1Dist x v ≤ zdL1Dist x w + zdL1Dist w v := zdL1Dist_triangle x w v
          _ ≤ k * R + R := Nat.add_le_add hwd hstep.2.2
          _ = (k + 1) * R := by ring
    exact Finset.Subset.antisymm (hLsub k)
      fun u huU => hclosed u (hconn x hx u huU)
  -- Layer cardinality grows at least linearly until it saturates.
  have hcard : ∀ k, min (k + 1) U.card ≤ (layer x U R k).card := by
    intro k
    induction k with
    | zero =>
      have h1 : 0 < (layer x U R 0).card := Finset.card_pos.mpr ⟨x, hxL 0⟩
      omega
    | succ k ih =>
      by_cases hLU : layer x U R k = U
      · have hle : U.card ≤ (layer x U R (k + 1)).card := by
          calc U.card = (layer x U R k).card := by rw [hLU]
            _ ≤ (layer x U R (k + 1)).card := Finset.card_le_card (hmono k)
        omega
      · have hlt := hgrow k hLU
        omega
  -- At radius index `U.card - 1` the layer is all of `U`.
  have hU1 : 0 < U.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hfull : layer x U R (U.card - 1) = U := by
    apply Finset.eq_of_subset_of_card_le (hLsub _)
    have h := hcard (U.card - 1)
    omega
  have hyL : y ∈ layer x U R (U.card - 1) := by rw [hfull]; exact hy
  calc zdL1Dist x y ≤ (U.card - 1) * R := (mem_layer.mp hyL).2
    _ = R * (U.card - 1) := Nat.mul_comm _ _

/-! ## Overlap-connected families of small-diameter sets are step-connected -/

/-- All pairs within each member set are within distance `R`. -/
def SmallSets (s : Finset (Region (Zd d))) (R : ℕ) : Prop :=
  ∀ A ∈ s, ∀ u ∈ A, ∀ v ∈ A, zdL1Dist u v ≤ R

/-- The support of an overlap-connected family of sets of diameter at most `R`
is `R`-step connected: move within a member set in one step, and across the
family along the overlap chain through shared points. -/
theorem stepConn_sup_of_overlapConn {s : Finset (Region (Zd d))} {R : ℕ}
    (hsmall : SmallSets s R) (hconn : OverlapConn s) :
    StepConn (s.sup id) R := by
  intro u hu v hv
  obtain ⟨A, hA, huA⟩ := Finset.mem_sup.mp hu
  obtain ⟨B, hB, hvB⟩ := Finset.mem_sup.mp hv
  have hmemU : ∀ {C : Region (Zd d)}, C ∈ s → ∀ {w : Zd d}, w ∈ C →
      w ∈ s.sup id := fun {C} hC {w} hw => Finset.mem_sup.mpr ⟨C, hC, hw⟩
  -- strengthened claim: `u` step-reaches every point of every set overlap-reachable
  -- from `A`
  have key : ∀ C, OverlapReach s A C →
      ∀ w ∈ C, Relation.ReflTransGen (StepIn (s.sup id) R) u w := by
    intro C hreach
    induction hreach with
    | refl =>
      intro w hw
      exact Relation.ReflTransGen.single
        ⟨hmemU hA huA, hmemU hA hw, hsmall A hA u huA w hw⟩
    | @tail C D _hAC hstep ih =>
      intro w hw
      obtain ⟨z, hz⟩ := hstep.2.2
      have hzC : z ∈ C := (Finset.mem_inter.mp hz).1
      have hzD : z ∈ D := (Finset.mem_inter.mp hz).2
      exact (ih z hzC).tail
        ⟨hmemU hstep.2.1 hzD, hmemU hstep.2.1 hw, hsmall D hstep.2.1 z hzD w hw⟩
  exact key B (hconn A hA B hB) v hvB

/-- A `StepIn U R`-chain is also a `StepIn V R`-chain for any larger `V`. -/
theorem reflTransGen_stepIn_mono {U V : Finset (Zd d)} {R : ℕ} {u v : Zd d}
    (h : Relation.ReflTransGen (StepIn U R) u v) (hUV : U ⊆ V) :
    Relation.ReflTransGen (StepIn V R) u v :=
  Relation.ReflTransGen.mono (fun _a _b hab => ⟨hUV hab.1, hUV hab.2.1, hab.2.2⟩) h

/-- The support of an overlap-connected family of `R`-step-connected sets is
itself `R`-step connected: move within a member using its own connectivity, and
across the family along the overlap chain through shared points. -/
theorem stepConn_sup_of_overlaps_chain {T : Finset (Finset (Zd d))} {R : ℕ}
    (hmem : ∀ U ∈ T, StepConn U R)
    (hconn : OverlapConn T) :
    StepConn (T.sup id) R := by
  intro u hu v hv
  obtain ⟨A, hA, huA⟩ := Finset.mem_sup.mp hu
  obtain ⟨B, hB, hvB⟩ := Finset.mem_sup.mp hv
  have hsub : ∀ {C : Finset (Zd d)}, C ∈ T → C ⊆ T.sup id := fun {C} hC =>
    Finset.le_iff_subset.mp (Finset.le_sup (f := id) hC)
  have key : ∀ C, OverlapReach T A C →
      ∀ w ∈ C, Relation.ReflTransGen (StepIn (T.sup id) R) u w := by
    intro C hreach
    induction hreach with
    | refl =>
      intro w hw
      exact reflTransGen_stepIn_mono (hmem A hA u huA w hw) (hsub hA)
    | @tail C D _hAC hstep ih =>
      intro w hw
      obtain ⟨z, hz⟩ := hstep.2.2
      have huz := ih z (Finset.mem_inter.mp hz).1
      have hzw := reflTransGen_stepIn_mono
        (hmem D hstep.2.1 z (Finset.mem_inter.mp hz).2 w hw) (hsub hstep.2.1)
      exact huz.trans hzw
  exact key B (hconn A hA B hB) v hvB

end PolymerKP
