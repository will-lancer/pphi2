/-
Umbrella module for the generic Kotecký–Preiss cluster-expansion engine,
mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/` @
origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Candidate for standalone-library extraction (planning/keystone-18-campaign.md
K18-0); keep divergence minimal.
-/
import Pphi2.ClusterExpansion.KP.Counting
import Pphi2.ClusterExpansion.KP.Expansion
import Pphi2.ClusterExpansion.KP.Geometry
import Pphi2.ClusterExpansion.KP.Graphs
import Pphi2.ClusterExpansion.KP.KPBound
import Pphi2.ClusterExpansion.KP.Overlap
import Pphi2.ClusterExpansion.KP.TsumFacts

/-!
# Generic Kotecký–Preiss cluster expansion (namespace `PolymerKP`)

A fully proved (no axioms, no sorries), spin/lattice-independent Kotecký–Preiss
engine for abstract hard-core polymer systems, following Friedli–Velenik
Chapter 5. Mirrored from the GibbsMeasure project; every file carries a
provenance header recording the source commit.

## Mirrored API surface

Core objects (`KPBound.lean`, `Expansion.lean`):

* `PolymerKP.PolymerSystem P` — abstract polymer system: `ℝ≥0∞`-valued absolute
  activities `W`, a symmetric reflexive incompatibility relation `bad`, and a
  nonnegative size function `a` for the Kotecký–Preiss condition.
* `PolymerKP.PolymerSystem.KPCondition` — the Kotecký–Preiss condition
  (FV (5.10)): `∑_{γ' bad γ} W γ' · exp (a γ') ≤ a γ` for every polymer `γ`.
* `PolymerKP.PolymerSystem.kp_rooted_bound` — the rooted cluster bound
  (FV Theorem 5.4): the sum over clusters rooted at `γ₀`, weighted by absolute
  Ursell factors and absolute activities, is at most `exp (a γ₀)`.
* `PolymerKP.PolymerSystem.kp_pinned_bound` — clusters pinned to a polymer
  predicate `r`, bounded by `exp` of the total tilted activity over `r`.
* `PolymerKP.PolymerSystem.kp_total_bound` — the total cluster sum, bounded by
  `exp` of the total tilted activity.
* `PolymerKP.Xi` — the hard-core polymer partition function
  `Ξ(w) = ∑_{T compatible} ∏_{γ ∈ T} w γ`.
* `PolymerKP.clusterSeries` — the signed cluster series
  `T(w) = ∑_clusters (n!)⁻¹ · Ursell · ∏ w` (FV (5.6), tuple form).
* `PolymerKP.PolymerSystem.Xi_eq_exp_clusterSeries` — the cluster expansion
  identity `Ξ(w) = exp (T(w))` (FV Proposition 5.3 + §5.6) under `KPCondition`
  and a finite total tilted activity.

Supporting infrastructure:

* `Graphs.lean` — graphs as edge Finsets on a finite vertex set: reachability
  (`Reach`), connected spanning edge sets (`ConnOn`), the sums
  `graphSum`/`connSum`, the component decomposition (FV (5.7)), the exponential
  formula, and the star decomposition used in the KP induction.
* `Overlap.lean` — overlap components of a finite family of finite sets:
  `Overlaps`, `OverlapConn`, `overlapComponents`, uniqueness of the
  decomposition into overlap-connected, support-disjoint subfamilies.
* `Counting.lean` — counting lemmas relating set partitions to fibered
  functions into `Fin k`.
* `TsumFacts.lean` — `tsum` infrastructure: finite dependent Fubini,
  tuple-power identities, fiber factorization, symmetrization
  (tuples ↔ `n!` × finite sets).
* `Geometry.lean` — `ℓ¹` lattice geometry on `ℤ^d` (`Zd`, `zdL1Dist`,
  `StepConn`) for finite-range tail bounds; the three lattice definitions are
  inlined from GibbsMeasure `Ch6Subtree/Foundations/Lattice.lean`.

## Reference

Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Chapter 5.
-/
