# pphi2 construction completion plan

Status: `executing`

## Plan header

- Primary gate: prove `Pphi2.cylinderIso_OS_of_RP_OS2` with the public type in `Pphi2/AsymTorus/AsymContinuumLimit.lean` and the final footprint `[propext, Classical.choice, Quot.sound, GaussianField.embed_l2_uniform_bound]`.
- Repository endpoint: complete the active `Pphi2` and `Common` build under `goal.md`, `goal_part_b.md`, `goal_part_c.md`, and `goal_part_d.md`, ending with one weak-coupling quartic plane measure carrying the full OS package, positive two-point form, and nonzero connected four-point function.
- Canonical checkout: `/Users/wlancer/Research/Douglas/pphi2`.
- Last remotely checked Part A baseline: `codex/pphi2-part-a` at `7cf129f32cc10b35c06a9eb7637f4a6524e86248`. The current branch contains follow-up compiler repair `b7ebef3177da1ca870092922dc14ef1e06b71118` plus this plan. Replacement workflows must target the resulting exact branch SHA.
- Preserved worktrees: Part B at `bd00c09e61749a4c9364e0c530ba28f3b064a761`, Part C at `b8ddd66afe2ce3f38ee722277a3da27939005b45`, and Part D at `5029f5a951d658e9867ab04ce1f9e273c0a6a728`. Each contains uncommitted user-owned work.
- Historical integration reference: `codex/pphi2-integrate` at `589eb07bfea913540f075ecdc020a91638152f80`. Its base predates the current Part A route, so it remains reference material.
- Other reference worktrees: `codex/pphi2-part-a-pr` at `cd9e08c9898c919eb15c9938b9a9c4887f9f0338` and `codex/pr62-minimal-rebuild` at `be3cc61e1c5451d75e31b879445082e74ccce866`. Both remain reference-only under the no-PR boundary.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Dependency pins: Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; GaussianField `d63a28568a75d99f6cb27af1f888a49a69855a66`; reflection-positivity `1cf718319c8f3b6ff3724a1a5781110aa9fc0630`; lee-yang `d48ee59243afb5e30a3de3ccc90eae2d51806537`; GibbsVariational `a7535d19a2744f64642823f1dc4da573188d4f13`; MarkovSemigroups `acf649108ea2222f4a8544a2782f448cb502492a`.
- Allowed local commands: bounded `rg`, `sed`, `git status`, `git diff`, `git show`, `git log`, `git worktree list`, `git diff --check`, and the source-only axiom scanner. Edits use `apply_patch`.
- Allowed remote commands: branch pushes to the named `codex/pphi2-part-*` branches on the user fork, workflow dispatch, compact GitHub Actions log inspection, clean remote Lake builds, and remote axiom generation.
- Local limits: preserve the existing ignored `.lake`; run no local Lean, Lake, toolchain install, broad clone, large download, Python proof search, or numerical campaign.
- External-action limit: create no pull request, merge, release, force-push, branch deletion, repository-setting change, or upstream write.
- Completion tests: exact-SHA CI and assurance; fresh kernel reports; zero new `axiom`, `sorry`, `admit`, unsafe declaration, or trusted bypass; source-quantifier review; clean index; local-only ledgers excluded; final cross-part consumer trace.

## Background

### Contracts and repository state

`goal.md` controls the first release gate. The current cylinder theorem is quartic and takes `P : InteractionPolynomial`, `hP : P.n = 4`, `mass : ℝ`, and `hmass : 0 < mass`, under `[Fact (0 < Ls)]`. Its proof already calls `asymInteracting_expMoment_volume_uniform_absForm_thresholded`. The dormant declaration `asymInteracting_expMoment_volume_uniform` is outside the live headline path.

Part B owns fixed-circumference cylinder OS4. Part C owns the coupled plane limit, plane inheritance, Green convergence, clustering, rotation control, and plane OS assembly. Part D owns the KP/BKAR uniqueness program, interaction witnesses, and the final one-measure headline. Parts B through D have divergent histories and uncommitted changes. Integration begins from reviewed packet commits, with file ownership resolved before each merge.

The dated filtered source scan on 2026-08-30 finds 25 project axiom declarations and zero real sorries. This is inventory evidence. `audit/axiom-report.txt`, `status.md`, `docs/AXIOM_STATUS.md`, and parts of the planning tree contain dated claims. Kernel output from one exact commit controls release status.

### Part A definitions and conventions

The live chain is:

```text
cylinderIso_OS_of_RP_OS2
  -> asymInteracting_expMoment_volume_uniform_absForm_thresholded
  -> asymInteracting_expMoment_absForm_thresholded
  -> asymInteracting_expMoment_of_signed
  -> asymInteracting_mgf_gaussianDominated
  -> asymInteractingVariance_le_freeVariance_lattice_thresholded
```

The six live project inputs are `asymInteracting_mgf_gaussianDominated`, `fss_infrared_quadratic`, `asymTransferGap_uniform_fixedLs`, `asymFinitePeriodicBridge_diagonal_bound`, `asymFinitePeriodicBridge_remainder_bound_uniform`, and `groundVariance_le_freeCovariance`.

The seventh forbidden declaration, `asymInteracting_expMoment_volume_uniform`, is dormant on this edge. Dormancy supplies no discharge proof.

The scaling convention is `Ns * a = Ls` and `Nt * a = Lt`, with `a > 0`, `mass > 0`, `a <= a0`, and `L0 <= Lt`. The cylinder infrared limit sends `Lt` to infinity at fixed positive `Ls`. The bridge window fixes `tau > 0`, assumes `2 * tau <= Nt * a`, and uses `gamma ^ (Nt - Nat.ceil (tau / a))`. Truncation estimates remain uniform in `K`.

Layer A applies only to quartic interactions and sitewise nonnegative sources. Signed sources enter through positive and negative parts. Mixed-sign Newman domination and the all-even-degree extension fail on finite examples recorded in the audit. The current lee-yang pin supplies finite Ising, Asano, unit-circle, Newman, and abstract Griffiths-Simon APIs. It lacks the shared-spin Wick quartic producer.

The B2 high branch is the FSS zero-mode-complement estimate with the exact `(a^2)^-1` normalization. Its low branch uses fixed-`Ls` transfer contraction, finite-periodic diagonal and residual estimates, ground-state slice comparison, and the proved band-to-free result. Pointwise positive lattice gaps do not supply the uniform physical gap.

Existing APIs for the first bridge packet include `pathTwoPoint_eq_traceRatio_val`, `rankOne_kernel_split`, `trace_product_integrand_expansion`, and the transfer-power kernel identities. The first theorem retains a scalar residual for fixed parameters. Uniform IUC estimates form later packets.

### Part B definitions and consumers

The current Part B branch contains a conditional weighted-kernel and block-clustering pipeline. Its terminal theorem must state OS4 for the constructed cylinder measure. The transfer gap and periodic bridge inputs disappear from the final public theorem after Part A integration. Constants remain uniform in every UV and temporal parameter used by the weak limit.

Observable approximation proceeds from bounded slice truncations to the characteristic-functional class used by cylinder OS4. Each passage records domination, integrability, and uniformity. The regime remains fixed positive `Ls`; spatial-volume-uniform clustering belongs to Part C.

### Part C definitions and consumers

`Pphi2.IsPphi2Limit` requires actual approximants `continuumMeasure 2 (N k) P (a k) mass`, together with `a k -> 0`, `N k -> infinity`, and `N k * a k -> infinity`. Fixed-volume Prokhorov extraction supplies no inhabitant of this predicate.

The open Part C producers are `pphi2_limit_exists`, `continuum_exponential_moment_bound`, `canonical_continuumMeasure_cf_tendsto`, `continuum_exponential_clustering`, `rotation_cf_defect_polylog_bound`, and `latticeGreenBilinear_basis_tendsto_continuum`. The direct Ward route avoids `os2_from_phi4`; legacy Bridge consumers still use it.

The implementation of `continuumGreenBilinear` and its Fourier-space documentation require one settled convention before the propagator packet. Plane clustering requires an explicit weak-coupling or single-phase input and spatial-volume-uniform constants. The current `ward_identity_lattice` is an algebraic identity and supplies no rotated-observable estimate.

### Part D definitions and consumers

Part D requires an axiom-free generic KP engine, continuous-spin measurable foundations, a finite AR/BKAR formula with Schur-product positivity, integrated covariance activity bounds, fixed-spacing boundary independence, coupled-limit uniqueness, and one-measure interaction witnesses.

The current `isPhi4` and weak-coupling predicates do not pin the polynomial coefficients. `continuumLimit_nonGaussian` constructs a separate witness, while `pphi2_limit_exists` constructs the plane limit. The final theorem needs one measure satisfying every property.

The untracked `Pphi2/ClusterExpansion/` scaffold remains outside the active import graph until provenance and remote compilation are recorded. The finite-partition bridge will use `Finpartition.toSubtype`, `Finpartition.mem_toSubtype_iff`, `Finset.preimage_map`, `Finpartition.ofPairwiseDisjoint`, `PerfectMatchingOn.ext`, and the existing Grassmann left/right embeddings. Pfaffian sign transport is proved through a bijection on crossing pairs. Block Schur complements use the existing lexicographic embeddings.

### Mathematical sources and translation checks

The Layer A source set is Lee-Yang 1952, Asano 1970, Ruelle 1973, Simon-Griffiths 1973, and Newman 1975. The proof plan needs exact theorem-to-API maps for shared-spin approximation, root pairing, MGF convergence, variance convergence, and uniform integrability.

The FSS source is Frohlich-Simon-Spencer, *Communications in Mathematical Physics* 50 (1976), Theorems 2.1 through 2.3 on pages 81 through 83. Its finite periodic zero-mode-complement estimate still needs an asymmetric GJ normalization adapter. Jäkel-Robl, arXiv:1103.3609v3, section 2.4 and Theorem 2.6, together with Heifets-Osipov, *Communications in Mathematical Physics* 56 (1977), pages 161 through 172, supplies fixed-circle spectral information. The uniform lattice family still needs spectral convergence.

For Part C, Frohlich, *Helvetica Physica Acta* 47 (1974), Theorems A.1 and 4.2 on page 296, is the relevant two-dimensional infinite-volume source. The companion Part II paper is *Advances in Mathematics* 23 (1977), pages 119 through 180; the repository's 1976 date is wrong. Park, *Journal of Mathematical Physics* 18 (1977), pages 354 through 366, treats a three-dimensional model. The old Part C Park citation cannot support the two-dimensional coupled-limit claim. The exact adapter from Frohlich's construction to `IsPphi2Limit` remains open.

The Part D activity estimate uses integrated adjacent-block covariance bounds of the form `a^4 * sum |C(x,y)|^k <= Ck`. A pointwise adjacent-block estimate has insufficient scaling.

### Verification surfaces

GitHub Actions `CI` runs the default Lake build. `assurance` runs the clean build, golden axiom comparison, and sorry confinement. Its current L1 report mismatch is warn-only. A green assurance result therefore accompanies a manually checked fresh report.

The exact Part A repair runs are CI `33348110878` and assurance `33348112749`, both targeting `7cf129f32cc10b35c06a9eb7637f4a6524e86248`. Their final results and logs remain part of the baseline packet.

Every implementation packet gets one file owner, a source-level review, a remote focused or full build, an axiom delta, and a clean handoff commit. The final composite branch is rebuilt from reviewed packet commits. The historical integration branch supplies comparison material only.

## Proof

### Dependency graph

```text
Part A Layer A producer ----+
Part A FSS -----------------+
Part A fixed-Ls gap --------+-- Part A thresholded variance
Part A diagonal bridge -----+             |
Part A remainder bridge ----+             v
Part A B5b -----------------+-- cylinder OS0/OS1/OS2/OS3
                                             |
                                             +-- Part B cylinder OS4

Part A moments -------------------------------+
Part B physical clustering -------------------+-- Part C coupled plane limit and OS
Part C Green and rotation packets -------------+             |
                                                             v
Part D KP/BKAR -> activity -> boundary uniqueness -> coupled uniqueness
                                                             |
Part C plane witness -----------------------------------------+
                                                             v
                                       one-measure interacting headline
```

### Part A argument

Construct a semantic finite-lattice ferromagnetic Wick Gibbs density. Build shared-spin Ising approximants for the quartic one-site factor. Derive paired unit-circle roots and the exact cosh product. Prove MGF and variance convergence with uniform integrability. Package these results as `AsymWickPhi4IsingApproximants`, feed `asymInteracting_mgf_gaussianDominated_of_griffithsSimon`, and replace the Layer A axiom call.

For high temporal modes, prove the quartic FSS quadratic estimate on the zero-mode complement. Preserve the asymmetric Fourier order, mass threshold, and `a^2` factors. For low modes, prove fixed-parameter trace splitting first. Add K-uniform diagonal and periodic residual estimates at fixed physical `tau`. Establish norm-resolvent or collectively compact convergence for the fixed-`Ls` transfer family, obtaining one `m0` and `a0`. Prove the B5b ground/free one-slice comparison with the matching GJ covariance normalization.

The existing thresholded variance assembly combines these inputs. The signed-source theorem applies Layer A to doubled positive and negative parts, then uses covariance positivity to obtain the sitewise-absolute free variance. The torus pushforward and thresholded grid family supply the cylinder exponential moment. Existing UV, IR, OS2, and no-wrap reflection-positive limit arguments finish the cylinder theorem.

### Part B argument

Review and compile the conditional weighted-kernel pipeline in its own worktree. Prove the normalized-kernel semigroup and row-smoothing results, followed by block clustering. Connect the fixed-`Ls` transfer contraction and periodic estimates from Part A. Extend from truncated slice observables through a uniform approximation theorem. Pass connected clustering through the cylinder weak limit and publish the OS4 cylinder theorem.

### Part C argument

Settle the continuum Green convention. Prove the flat Fourier identities, periodic infrared comparison, joint UV basis limit, and full bilinear convergence. Derive canonical characteristic-functional convergence from the coupled sequence with a tail reindexing lemma.

Use Part A moment bounds to obtain uniform integrability and mixed Green-form exponential moments. Construct a diagonal coupled sequence of actual lattice measures with simultaneous tightness, characteristic-functional convergence, translation control, reflection positivity, and moment convergence. Package every field of `IsPphi2Limit`.

Thread Part B clustering through the spatial thermodynamic limit under an explicit phase condition. Prove the genuine rotated-observable Ward estimate and its uniform defect bound. Assemble the plane OS package on the coupled-limit witness and remove the live Part C inheritance axioms.

### Part D argument

Certify the source and license of the generic KP material, then port it without active pphi2 imports. Prove the finite-set Pfaffian/principal-submatrix bridge using a finite-set order isomorphism, partition transport, crossing-pair cardinality, and endpoint preservation. Establish the AR/BKAR identity, block Schur positivity, and continuous-spin measurable activity interface.

Combine integrated covariance, Nelson, Wick-moment, and hypercontractive bounds to prove an `a`-uniform KP row-sum estimate. Derive fixed-spacing boundary independence and uniform cluster tails. Pass these bounds through the coupled limit, identify all subsequential Schwinger functions, and use the existing moment-determinacy theorem to prove `pphi2_limit_unique`.

Replace the placeholder quartic and weak-coupling predicates with coefficient-aware definitions. Transport positive two-point and strict connected-four-point witnesses to the unique plane measure. Rewrite `schwinger_agreement`, `pphi2_nontriviality`, and `continuumLimit_nonGaussian` as theorems about that measure. Add the final public one-measure headline.

### Recovery routes

- If the shared-spin root-pairing statement needs new upstream lee-yang APIs, implement a pphi2-local theorem first and preserve authorship. B2 and Part B proceed in parallel.
- If norm-resolvent convergence is unavailable, prove collectively compact semigroup convergence at one fixed physical time and extract the isolated eigenvalue gap.
- If uniform IUC is too strong, retain the fixed-parameter trace split and prove only the diagonal and residual estimates consumed by the thresholded theorem.
- If the Green convention audit changes a public definition, stop the Part C propagator packet until every consumer and normalization is remapped.
- If the KP provenance cannot be certified, reimplement the small generic core from published statements and keep the recovered scaffold outside the import graph.
- If a source theorem carries extra phase assumptions, add the explicit predicate at the earliest public boundary and propagate it through consumers.

## Adversarial audit

| ID | Section | Severity | Evidence and consequence | Disposition |
|---|---|---|---|---|
| AUD-001 | Plan header | major | The old plan named `2e49df7`; current work is `7cf129f`. Remote evidence could target the wrong tree. | Header and run IDs now name the exact repair commit. |
| AUD-002 | Repository state | major | `codex/pphi2-integrate` diverges from current Part A across 186 files and lacks the latest route. | Preserve it as reference and build a fresh composite from reviewed packets. |
| AUD-003 | Part A Layer A | fatal | `AsymWickPhi4IsingApproximants` stores abstract functions without semantic Ising measures. Filling fields could relocate the axiom. | Require shared-spin measures, root pairing, MGF convergence, variance convergence, and uniform integrability before construction. |
| AUD-004 | Part A Layer A | fatal | Mixed-sign and all-even-degree Newman strengthenings have finite counterexamples. | Keep `P.n = 4` and sitewise nonnegative sources; recover signed inputs through the proved split. |
| AUD-005 | Part A B2 | major | Dated prose calls B2 discharged while five analytic inputs remain axioms. | Name all five producers and give each an independent packet. |
| AUD-006 | Fixed-Ls gap | fatal | Per-lattice Jentzsch gaps do not imply a positive family infimum. | Require spectral convergence controlling the coupled `Ns * a = Ls` family. |
| AUD-007 | FSS | major | The pinned Chessboard module contains no usable FSS theorem. | Treat FSS as an analytic producer with a source-normalization proof. |
| AUD-008 | Periodic bridge | major | Generic GroundBridge lemmas leave the concrete trace dictionary and K-uniform estimates open. | Split fixed-parameter trace identity from uniform diagonal and residual analysis. |
| AUD-009 | DDJ route | major | `AsymDoubledSourcePressureBound` is conditional and does not imply the Newman comparator. | Keep DDJ as a separate source-pressure lane. |
| AUD-010 | Part B worktree | major | Seven modified and three new files are uncommitted user-owned work. | Audit, partition, and commit only reviewed coherent packets. |
| AUD-011 | Part C existence | fatal | Fixed-volume extraction cannot inhabit the coupled `IsPphi2Limit` predicate. | Build an actual diagonal UV/IR sequence and prove every predicate field. |
| AUD-012 | Part C Green form | fatal | The implementation and Fourier-space documentation disagree. | Freeze a convention theorem before propagator work. |
| AUD-013 | Part C clustering | major | The current plane clustering axiom has no phase hypothesis or spatial uniformity. | Introduce an explicit spatially uniform phase-aware input and prove its limit transfer. |
| AUD-014 | Part C rotation | major | `ward_identity_lattice` subtracts identical expressions and supplies no rotation estimate. | Prove a rotated-observable identity and the required uniform defect. |
| AUD-015 | Part D predicate | fatal | The current weak-coupling predicate ignores `P`; `isPhi4` leaves coefficients detached. | Define coefficient-aware quartic and weak-coupling structures before uniqueness assembly. |
| AUD-016 | Part D witness | fatal | Plane existence, nontriviality, and nonGaussianity refer to different measures. | Prove coupled-limit uniqueness before one-measure packaging. |
| AUD-017 | Part D provenance | major | The KP/BKAR scaffold is untracked and cites an unavailable source revision. | Keep it out of active imports until provenance and remote compile evidence pass. |
| AUD-018 | Evidence | major | Assurance L1 permits a stale golden report. | Inspect fresh kernel output and commit the synchronized golden separately. |
| AUD-019 | Local state | moderate | `goal.md` says `.lake` is absent, while an ignored 9.3 GB tree exists. | Preserve it and run every Lean check remotely. |
| AUD-020 | Worktree ownership | major | Parts B, C, and D contain overlapping uncommitted files. | Use one owner per file and integrate through reviewed commits. |
| AUD-021 | Sources | major | The audit identifies Park 1977 as three-dimensional and Frohlich 1974 as the relevant two-dimensional source. | Prove the adapter from Frohlich's hypotheses and construction to the exact coupled `IsPphi2Limit` predicate. |
| AUD-022 | External action | major | The task authorizes progress while the user withheld PR creation. | Push only verification branches to the fork and create no PR. |

## Atomic enumeration

### Background items

- [x] BG-001 | phase: P0 | packet: PKT-00 | deps: none | owner: root | status: done | output: Part A contract | evidence: `goal.md` | task: Read the full Part A stopping condition.
- [x] BG-002 | phase: P0 | packet: PKT-00 | deps: none | owner: part-b-contract | status: done | output: Part B contract | evidence: `goal_part_b.md` audit | task: Extract the OS4 completion boundary.
- [x] BG-003 | phase: P0 | packet: PKT-00 | deps: none | owner: part-cd-contract | status: done | output: Part C contract | evidence: `goal_part_c.md` audit | task: Extract the coupled-plane completion boundary.
- [x] BG-004 | phase: P0 | packet: PKT-00 | deps: none | owner: part-cd-contract | status: done | output: Part D contract | evidence: `goal_part_d.md` audit | task: Extract the uniqueness and one-measure boundary.
- [x] BG-005 | phase: P0 | packet: PKT-00 | deps: none | owner: root | status: done | output: canonical worktree map | evidence: `git worktree list --porcelain` | task: Resolve every active checkout and branch.
- [x] BG-006 | phase: P0 | packet: PKT-00 | deps: none | owner: root | status: done | output: pinned environment | evidence: `lean-toolchain`; `lake-manifest.json` | task: Record the toolchain and dependency revisions.
- [x] BG-007 | phase: P1 | packet: PKT-01 | deps: BG-005 | owner: root | status: done | output: axiom inventory | evidence: bounded source declaration scan | task: Enumerate the live project axioms.
- [x] BG-008 | phase: P2 | packet: PKT-01 | deps: BG-001, BG-007 | owner: headline-trace | status: done | output: cylinder dependency graph | evidence: declaration-to-consumer trace | task: Trace the live Part A headline.
- [x] BG-009 | phase: P2 | packet: PKT-01 | deps: BG-001, BG-007 | owner: layer-a-frontier | status: done | output: Layer A frontier | evidence: `AsymInteractingLeeYang.lean` audit | task: Locate the missing semantic Newman producer.
- [x] BG-010 | phase: P2 | packet: PKT-01 | deps: BG-001, BG-007 | owner: layer-b2-frontier | status: done | output: B2 frontier | evidence: five declaration and consumer traces | task: Separate the proved shell from its analytic inputs.
- [x] BG-011 | phase: P1 | packet: PKT-02 | deps: BG-005 | owner: part-b-diff-audit | status: done | output: Part B ownership inventory | evidence: worktree status and diff audit | task: Classify the Part B uncommitted files.
- [x] BG-012 | phase: P1 | packet: PKT-02 | deps: BG-005 | owner: part-c-diff-audit | status: done | output: Part C ownership inventory | evidence: 13-file diff audit | task: Classify the Part C uncommitted files.
- [x] BG-013 | phase: P1 | packet: PKT-02 | deps: BG-005 | owner: part-d-diff-audit | status: done | output: Part D ownership inventory | evidence: scaffold and diff audit | task: Classify the Part D uncommitted files.
- [x] BG-014 | phase: P1 | packet: PKT-02 | deps: BG-005 | owner: integration-branch-audit | status: done | output: historical integration verdict | evidence: merge-base and 186-file comparison | task: Decide whether the old integration branch is reusable.
- [x] BG-015 | phase: P3 | packet: PKT-01 | deps: BG-007, BG-008 | owner: evidence-audit | status: done | output: certificate drift report | evidence: generator and golden comparison | task: Audit the tracked axiom report.
- [x] BG-016 | phase: P1 | packet: PKT-00 | deps: BG-005 | owner: root | status: done | output: local resource boundary | evidence: ignored-tree inspection and goal policy | task: Record the remote-only Lean constraint.
- [x] BG-017 | phase: P3 | packet: PKT-A1 | deps: BG-006, BG-009 | owner: roadmap-lean-lead | status: done | output: lee-yang API map | evidence: pinned source signatures | task: Map paired-factor and Griffiths-Simon APIs.
- [x] BG-018 | phase: P3 | packet: PKT-A4 | deps: BG-006, BG-010 | owner: roadmap-math-lead | status: done | output: FSS translation risks | evidence: FSS source and Chessboard audit | task: Record normalization and missing reflection-positive input.
- [x] BG-019 | phase: P3 | packet: PKT-A5 | deps: BG-006, BG-010 | owner: source-citation-audit | status: done | output: spectral source map | evidence: primary papers | task: Verify the finite-circle and lattice-uniform gap claims.
- [x] BG-020 | phase: P3 | packet: PKT-A6 | deps: BG-006, BG-010 | owner: b2-trace-split-packet | status: done | output: trace API map | evidence: GroundBridge and transfer-kernel signatures | task: Identify the fixed-parameter bridge primitives.
- [x] BG-021 | phase: P3 | packet: PKT-AX | deps: BG-009 | owner: ddj-frontier | status: done | output: separate pressure route | evidence: `AsymUniformTiltedMoment.lean` trace | task: Classify the DDJ producer and its exact missing bound.
- [x] BG-022 | phase: P2 | packet: PKT-B0 | deps: BG-011 | owner: part-b-contract | status: done | output: Part B consumer graph | evidence: branch declarations and goal contract | task: Map conditional OS4 inputs to the public theorem.
- [x] BG-023 | phase: P2 | packet: PKT-C0 | deps: BG-012 | owner: part-cd-contract | status: done | output: `IsPphi2Limit` field map | evidence: `Embedding.lean` declaration audit | task: Record every coupled-limit field.
- [x] BG-024 | phase: P3 | packet: PKT-C0 | deps: BG-023 | owner: part-cd-contract | status: done | output: Green convention blocker | evidence: implementation and doc comparison | task: Locate the continuum Green mismatch.
- [x] BG-025 | phase: P3 | packet: PKT-C0 | deps: BG-023 | owner: part-cd-contract | status: done | output: Ward blocker | evidence: `ward_identity_lattice` body audit | task: Distinguish the algebraic identity from rotation control.
- [x] BG-026 | phase: P2 | packet: PKT-D0 | deps: BG-013 | owner: part-d-diff-audit | status: done | output: KP provenance-gap record | evidence: `PROVENANCE.md` and history audit | task: Record the unresolved source revision, license, and CI evidence.
- [x] BG-027 | phase: P2 | packet: PKT-D1 | deps: BG-013 | owner: delegated-bridge-audit | status: done | output: Pfaffian bridge API map | evidence: exact Finpartition and crossing-pair APIs | task: Specify finite-set reindexing without a global coordinate equivalence.
- [x] BG-028 | phase: P2 | packet: PKT-D0 | deps: BG-004, BG-007 | owner: part-cd-contract | status: done | output: predicate defect report | evidence: `Convergence.lean` definitions | task: Audit quartic and weak-coupling predicates.
- [x] BG-029 | phase: P2 | packet: PKT-02 | deps: BG-011, BG-012, BG-013 | owner: root | status: done | output: cross-worktree ownership rule | evidence: status inventories | task: Reserve one owner for each overlapping file.
- [x] BG-030 | phase: P1 | packet: PKT-03 | deps: BG-005 | owner: root | status: done | output: workflow map | evidence: `.github/workflows/ci.yml`; assurance workflow | task: Record remote build and certificate commands.
- [x] BG-031 | phase: P2 | packet: PKT-03 | deps: BG-006, BG-030 | owner: root | status: done | output: two failed exact-SHA runs | evidence: CI 33348110878; assurance 33348112749 | task: Capture both final remote results.
- [x] BG-032 | phase: P3 | packet: PKT-03 | deps: BG-008, BG-031 | owner: root | status: done | output: current local ledger | evidence: `LOCAL_GOAL_PROGRESS.md` current verification section | task: Replace stale branch, SHA, and certificate claims.
- [x] BG-033 | phase: P1 | packet: PKT-C0 | deps: BG-003, BG-006 | owner: source-citation-audit | status: done | output: plane-existence citation map | evidence: primary papers and official archives | task: Resolve the Park and Frohlich source conflict.
- [x] BG-034 | phase: P3 | packet: PKT-04 | deps: BG-008, BG-009, BG-010, BG-014, BG-023, BG-028 | owner: root | status: done | output: adversarial findings | evidence: AUD-001 through AUD-022 | task: Encode fatal and major plan repairs.
- [x] BG-035 | phase: P4 | packet: PKT-04 | deps: BG-015, BG-030 | owner: root | status: done | output: release gate definition | evidence: plan header and audit policy | task: Freeze the exact acceptance tests.
- [x] BG-036 | phase: P2 | packet: PKT-02 | deps: BG-005, BG-014 | owner: integration-branch-audit | status: done | output: fresh-composite rule | evidence: merge-base `2c3b0a2` | task: Retire the historical integration branch as a merge target.
- [x] BG-037 | phase: P1 | packet: PKT-01 | deps: BG-002, BG-003, BG-004 | owner: stream-contracts | status: done | output: stream overlap table | evidence: all `goal_stream_*.md` files | task: Map narrow streams into Parts A through D.
- [ ] BG-038 | phase: P4 | packet: PKT-A1 | deps: BG-017, BG-019 | owner: root | status: active | output: completed hard-source page map | evidence: FSS pp. 81-83; Jäkel-Robl section 2.4 and Theorem 2.6; Heifets-Osipov 56 (1977) 161-172 | task: Add exact Layer A, periodic-IUC, and B5b source locations to the verified FSS and fixed-circle map.
- [x] BG-039 | phase: P3 | packet: PKT-02 | deps: BG-029, BG-036 | owner: root | status: done | output: packet integration policy | evidence: one-owner and reviewed-commit rules | task: Define safe cross-worktree integration.
- [ ] BG-040 | phase: P5 | packet: PKT-04 | deps: BG-031, BG-032, BG-033, BG-038 | owner: root | status: blocked | output: frozen execution baseline | evidence: plan review and exact remote certificate | task: Close the remaining source map and obtain a green exact-SHA baseline.

### Proof items

- [x] PF-001 | phase: P4 | packet: PKT-A0 | deps: BG-015, BG-016 | owner: root | status: done | output: compiler repair patch | evidence: reviewed 22-file source diff | task: Replay the proof-only Lean compatibility fixes.
- [x] PF-002 | phase: P5 | packet: PKT-A0 | deps: PF-001 | owner: root | status: done | output: clean static patch | evidence: `git diff --check`; source axiom scan | task: Run bounded static verification.
- [x] PF-003 | phase: P6 | packet: PKT-A0 | deps: PF-002 | owner: root | status: done | output: repair commit `7cf129f` | evidence: git commit | task: Commit the reviewed repair set.
- [x] PF-004 | phase: P7 | packet: PKT-A0 | deps: PF-003 | owner: root | status: done | output: fork branch | evidence: `fork/codex/pphi2-part-a` at `7cf129f` | task: Push the repair commit for remote verification.
- [x] PF-005 | phase: P8 | packet: PKT-A0 | deps: PF-004, BG-030 | owner: root | status: done | output: exact-SHA CI run | evidence: run 33348110878 | task: Dispatch the clean remote build.
- [x] PF-006 | phase: P8 | packet: PKT-A0 | deps: PF-004, BG-030 | owner: root | status: done | output: exact-SHA assurance run | evidence: run 33348112749 | task: Dispatch the remote assurance gate.
- [x] PF-007 | phase: P9 | packet: PKT-A0 | deps: PF-005 | owner: root | status: done | output: CI failure in `AsymLatticeMeasure` | evidence: run 33348110878 | task: Inspect the remote build result.
- [x] PF-008 | phase: P9 | packet: PKT-A0 | deps: PF-006 | owner: root | status: done | output: assurance failure with sorry guard passing | evidence: run 33348112749 | task: Inspect report synchronization and sorry confinement.
- [ ] PF-009 | phase: P4 | packet: PKT-A1 | deps: BG-009, BG-017 | owner: layer-a-density | status: ready | output: density-bridge signature | evidence: exact existing density and energy lemmas | task: Freeze the finite-lattice ferromagnetic Wick Gibbs theorem.
- [ ] PF-010 | phase: P5 | packet: PKT-A1 | deps: PF-009 | owner: layer-a-density | status: queued | output: bond factorization lemma | evidence: focused remote compile | task: Express the quadratic action with nonnegative edge couplings.
- [ ] PF-011 | phase: P5 | packet: PKT-A1 | deps: PF-009 | owner: layer-a-density | status: queued | output: one-site Wick factor lemma | evidence: focused remote compile | task: Identify the quartic Wick site density.
- [ ] PF-012 | phase: P6 | packet: PKT-A1 | deps: PF-010, PF-011 | owner: layer-a-density | status: queued | output: normalized Gibbs-density theorem | evidence: remote theorem check and source review | task: Prove the semantic finite-lattice density bridge.
- [ ] PF-013 | phase: P5 | packet: PKT-A2 | deps: BG-017, BG-038 | owner: unassigned | status: blocked | output: shared-spin finite model | evidence: source theorem map and remote compile | task: Define the ferromagnetic shared-spin approximants.
- [ ] PF-014 | phase: P6 | packet: PKT-A2 | deps: PF-013 | owner: unassigned | status: blocked | output: finite partition polynomial identity | evidence: exact coefficient theorem | task: Relate the shared-spin measure to its Lee-Yang polynomial.
- [ ] PF-015 | phase: P7 | packet: PKT-A2 | deps: PF-014 | owner: unassigned | status: blocked | output: unit-circle root theorem | evidence: pinned Asano and Lee-Yang APIs | task: Prove the roots lie on the unit circle.
- [ ] PF-016 | phase: P8 | packet: PKT-A2 | deps: PF-015 | owner: unassigned | status: blocked | output: paired-root enumeration | evidence: finite multiset conjugation proof | task: Pair roots with the required angle constraints.
- [ ] PF-017 | phase: P9 | packet: PKT-A2 | deps: PF-016 | owner: unassigned | status: blocked | output: exact cosh MGF factorization | evidence: polynomial normalization calculation | task: Remove the assumed MGF identity from the paired constructor.
- [ ] PF-018 | phase: P9 | packet: PKT-A2 | deps: PF-016 | owner: unassigned | status: blocked | output: finite variance identity | evidence: second derivative at zero | task: Remove the assumed variance identity from the paired constructor.
- [ ] PF-019 | phase: P10 | packet: PKT-A2 | deps: PF-017, PF-018 | owner: unassigned | status: blocked | output: semantic paired factorization | evidence: `PairedUnitCircleFactorization` theorem | task: Build the finite Newman data without escape hypotheses.
- [ ] PF-020 | phase: P7 | packet: PKT-A3 | deps: PF-012, PF-013 | owner: unassigned | status: blocked | output: quartic block-spin convergence | evidence: Simon-Griffiths theorem translation | task: Prove weak convergence of site approximants.
- [ ] PF-021 | phase: P8 | packet: PKT-A3 | deps: PF-020 | owner: unassigned | status: blocked | output: lattice product convergence | evidence: finite-product weak convergence | task: Lift one-site convergence to the interacting lattice.
- [ ] PF-022 | phase: P11 | packet: PKT-A3 | deps: PF-019, PF-021 | owner: unassigned | status: blocked | output: uniform exponential integrability | evidence: source-faithful domination bound | task: Control the approximant MGFs uniformly.
- [ ] PF-023 | phase: P9 | packet: PKT-A3 | deps: PF-021 | owner: unassigned | status: blocked | output: uniform second-moment integrability | evidence: moment-tail estimate | task: Control approximant variances uniformly.
- [ ] PF-024 | phase: P12 | packet: PKT-A3 | deps: PF-022 | owner: unassigned | status: blocked | output: MGF convergence theorem | evidence: remote theorem check | task: Prove convergence to `asymInteractingMgf`.
- [ ] PF-025 | phase: P10 | packet: PKT-A3 | deps: PF-023 | owner: unassigned | status: blocked | output: variance convergence theorem | evidence: remote theorem check | task: Prove convergence to the interacting variance.
- [ ] PF-026 | phase: P13 | packet: PKT-A3 | deps: PF-019, PF-024, PF-025 | owner: unassigned | status: blocked | output: `AsymWickPhi4IsingApproximants` inhabitant | evidence: constructor with semantic producers | task: Package the complete Griffiths-Simon approximants.
- [ ] PF-027 | phase: P14 | packet: PKT-A3 | deps: PF-026 | owner: unassigned | status: blocked | output: Layer A theorem | evidence: focused remote `#print axioms` | task: Replace the Gaussian-dominated MGF axiom call.
- [ ] PF-028 | phase: P5 | packet: PKT-A4 | deps: BG-018, BG-038 | owner: unassigned | status: blocked | output: asymmetric RP setup | evidence: reflection-positive action theorem | task: Prove the required lattice reflection positivity.
- [ ] PF-029 | phase: P6 | packet: PKT-A4 | deps: PF-028 | owner: unassigned | status: blocked | output: chessboard estimate | evidence: source-normalized remote theorem | task: Establish the finite torus chessboard bound.
- [ ] PF-030 | phase: P7 | packet: PKT-A4 | deps: PF-029 | owner: unassigned | status: blocked | output: source-tilt Gaussian domination | evidence: twice-differentiated partition inequality | task: Derive the integrated quadratic estimate.
- [ ] PF-031 | phase: P8 | packet: PKT-A4 | deps: PF-030 | owner: unassigned | status: blocked | output: zero-mode-complement formula | evidence: asymmetric DFT calculation | task: Match the FSS Fourier quadratic form.
- [ ] PF-032 | phase: P9 | packet: PKT-A4 | deps: PF-031 | owner: unassigned | status: blocked | output: `fss_infrared_quadratic` theorem | evidence: focused remote `#print axioms` | task: Replace the FSS axiom.
- [ ] PF-033 | phase: P10 | packet: PKT-A4 | deps: PF-032 | owner: reviewer | status: queued | output: FSS normalization review | evidence: coefficient and edge-case audit | task: Check mass threshold, zero sum, and `a^2` factors.
- [ ] PF-034 | phase: P5 | packet: PKT-A5 | deps: BG-019, BG-038 | owner: unassigned | status: blocked | output: continuum transfer family | evidence: exact operator definition | task: Define the fixed-`Ls` continuum comparison operator.
- [ ] PF-035 | phase: P6 | packet: PKT-A5 | deps: PF-034 | owner: unassigned | status: blocked | output: form convergence theorem | evidence: source and remote theorem check | task: Prove convergence of the lattice quadratic forms.
- [ ] PF-036 | phase: P7 | packet: PKT-A5 | deps: PF-035 | owner: unassigned | status: blocked | output: compact semigroup convergence | evidence: norm-resolvent or collective-compactness proof | task: Control the full small-`a` operator family.
- [ ] PF-037 | phase: P8 | packet: PKT-A5 | deps: PF-036 | owner: unassigned | status: blocked | output: isolated continuum eigenvalue | evidence: compact-resolvent spectral theorem | task: Identify the ground state and first excited gap.
- [ ] PF-038 | phase: P9 | packet: PKT-A5 | deps: PF-037 | owner: unassigned | status: blocked | output: uniform lattice spectral separation | evidence: spectral stability theorem | task: Exclude spurious low lattice eigenvalues.
- [ ] PF-039 | phase: P10 | packet: PKT-A5 | deps: PF-038 | owner: unassigned | status: blocked | output: physical contraction rate | evidence: exponential comparison | task: Choose one positive `m0` and small-`a` threshold.
- [ ] PF-040 | phase: P11 | packet: PKT-A5 | deps: PF-039 | owner: unassigned | status: blocked | output: `asymTransferGap_uniform_fixedLs` theorem | evidence: focused remote `#print axioms` | task: Replace the fixed-`Ls` gap axiom.
- [ ] PF-041 | phase: P12 | packet: PKT-A5 | deps: PF-040 | owner: reviewer | status: queued | output: gap quantifier review | evidence: coupled-scaling audit | task: Verify uniformity in `Nt`, `Ns`, and `a`.
- [ ] PF-042 | phase: P4 | packet: PKT-A6 | deps: BG-020 | owner: bridge-owner | status: ready | output: signed trace residual definition | evidence: focused remote compile | task: Define the fixed-parameter residual with its sign.
- [ ] PF-043 | phase: P5 | packet: PKT-A6 | deps: PF-042 | owner: bridge-owner | status: queued | output: trace-ratio algebraic split | evidence: focused remote compile | task: Prove the residual decomposition.
- [ ] PF-044 | phase: P6 | packet: PKT-A6 | deps: PF-043 | owner: bridge-owner | status: queued | output: path two-point dictionary | evidence: `pathTwoPoint_eq_traceRatio_val` application | task: Transport the split to the path observable.
- [ ] PF-045 | phase: P7 | packet: PKT-A6 | deps: PF-044 | owner: bridge-owner | status: queued | output: concrete asymmetric wrapper | evidence: remote theorem check | task: Match the shell hypothesis in `AsymSliceFamilySusceptibility`.
- [ ] PF-046 | phase: P4 | packet: PKT-A7 | deps: BG-020 | owner: unassigned | status: ready | output: kernel rank-one expansion | evidence: `rankOne_kernel_split` | task: Expand both finite-periodic kernel powers.
- [ ] PF-047 | phase: P5 | packet: PKT-A7 | deps: PF-046 | owner: unassigned | status: queued | output: trace numerator expansion | evidence: `trace_product_integrand_expansion` | task: Separate ground, mixed, and residual terms.
- [ ] PF-048 | phase: P6 | packet: PKT-A7 | deps: PF-047 | owner: unassigned | status: queued | output: partition denominator floor | evidence: positive ground eigenvalue trace theorem | task: Prove the denominator lower bound.
- [ ] PF-049 | phase: P7 | packet: PKT-A7 | deps: PF-048 | owner: unassigned | status: queued | output: diagonal finite-periodic estimate | evidence: K-uniform kernel bound | task: Control the single-slice diagonal correction.
- [ ] PF-050 | phase: P7 | packet: PKT-A7 | deps: PF-047, PF-048 | owner: unassigned | status: queued | output: signed residual estimate | evidence: Hilbert-Schmidt or IUC bound | task: Control the mixed and residual trace terms.
- [ ] PF-051 | phase: P8 | packet: PKT-A7 | deps: PF-049 | owner: unassigned | status: queued | output: `asymFinitePeriodicBridge_diagonal_bound` theorem | evidence: focused remote `#print axioms` | task: Replace the diagonal bridge axiom.
- [ ] PF-052 | phase: P8 | packet: PKT-A7 | deps: PF-050 | owner: unassigned | status: queued | output: `asymFinitePeriodicBridge_remainder_bound_uniform` theorem | evidence: focused remote `#print axioms` | task: Replace the periodic residual axiom.
- [ ] PF-053 | phase: P9 | packet: PKT-A7 | deps: PF-051, PF-052 | owner: reviewer | status: queued | output: bridge exponent review | evidence: `Nat.ceil` and wrap-distance audit | task: Verify the exact physical damping exponent.
- [ ] PF-054 | phase: P5 | packet: PKT-A8 | deps: BG-010, BG-038 | owner: unassigned | status: blocked | output: ground marginal identity | evidence: transfer ground-state measure theorem | task: Identify the infinite-time slice marginal.
- [ ] PF-055 | phase: P6 | packet: PKT-A8 | deps: PF-054 | owner: unassigned | status: blocked | output: one-slice Nelson estimate | evidence: source-normalized remote theorem | task: Bound interacting ground moments uniformly.
- [ ] PF-056 | phase: P7 | packet: PKT-A8 | deps: PF-055 | owner: unassigned | status: blocked | output: covariance factorization | evidence: GJ covariance identity | task: Match the free one-slice comparator.
- [ ] PF-057 | phase: P8 | packet: PKT-A8 | deps: PF-056 | owner: unassigned | status: blocked | output: uniform variance constant | evidence: fixed-`Ls` bound | task: Prove independence from `Nt`, slice, and fine `a`.
- [ ] PF-058 | phase: P9 | packet: PKT-A8 | deps: PF-057 | owner: unassigned | status: blocked | output: `groundVariance_le_freeCovariance` theorem | evidence: focused remote `#print axioms` | task: Replace the B5b axiom.
- [ ] PF-059 | phase: P10 | packet: PKT-A8 | deps: PF-058 | owner: reviewer | status: queued | output: B5b scaling review | evidence: lattice-spacing audit | task: Check the test-vector and covariance normalization.
- [ ] PF-060 | phase: P15 | packet: PKT-A9 | deps: PF-027, PF-032, PF-040, PF-051, PF-052, PF-058, PF-137, PF-138 | owner: root | status: blocked | output: axiom-free thresholded variance theorem | evidence: remote `#print axioms` | task: Recompile the existing assembly with all six producers on the certified compiler baseline.
- [ ] PF-061 | phase: P16 | packet: PKT-A9 | deps: PF-060 | owner: root | status: blocked | output: axiom-free signed exponential moment | evidence: remote `#print axioms` | task: Verify the positive-negative source split.
- [ ] PF-062 | phase: P17 | packet: PKT-A9 | deps: PF-061 | owner: root | status: blocked | output: axiom-free torus threshold theorem | evidence: remote `#print axioms` | task: Verify the torus pushforward and absolute form.
- [ ] PF-063 | phase: P18 | packet: PKT-A9 | deps: PF-062 | owner: root | status: blocked | output: Part A cylinder headline | evidence: exact remote kernel certificate | task: Verify the full cylinder OS0 through OS3 theorem.
- [ ] PF-064 | phase: P19 | packet: PKT-A9 | deps: PF-063 | owner: reviewer | status: queued | output: Part A source audit | evidence: independent quantifier and counterexample review | task: Approve the Part A mathematical footprint.

- [ ] PF-065 | phase: P2 | packet: PKT-B1 | deps: BG-011 | owner: part-b-owner | status: ready | output: Hilbert-Schmidt repair commit | evidence: focused remote compile | task: Isolate the one-line congruence repair.
- [ ] PF-066 | phase: P2 | packet: PKT-B1 | deps: BG-011 | owner: part-b-owner | status: ready | output: normalized-kernel semigroup module | evidence: focused remote compile | task: Verify the finite kernel composition identities.
- [ ] PF-067 | phase: P3 | packet: PKT-B1 | deps: PF-066 | owner: part-b-owner | status: queued | output: normalized-remainder semigroup module | evidence: focused remote compile | task: Verify the rank-one-subtracted composition identities.
- [ ] PF-068 | phase: P4 | packet: PKT-B1 | deps: PF-067 | owner: part-b-owner | status: queued | output: row-smoothing module | evidence: focused remote compile | task: Verify the conditional row-representative propagation.
- [ ] PF-069 | phase: P5 | packet: PKT-B1 | deps: PF-068 | owner: part-b-owner | status: queued | output: relative-IUC wrappers | evidence: focused remote compile | task: Verify the weighted-remainder consequences.
- [ ] PF-070 | phase: P6 | packet: PKT-B1 | deps: PF-065, PF-066, PF-067, PF-068, PF-069 | owner: root | status: queued | output: coherent Part B import commit | evidence: remote root build | task: Reconcile the aggregate `Pphi2.lean` imports.
- [ ] PF-071 | phase: P7 | packet: PKT-B1 | deps: PF-070 | owner: root | status: queued | output: Part B verification branch | evidence: fork branch SHA | task: Push the reviewed conditional-kernel packet.
- [ ] PF-072 | phase: P8 | packet: PKT-B1 | deps: PF-071 | owner: root | status: queued | output: Part B baseline certificate | evidence: exact-SHA CI and assurance | task: Compile the conditional pipeline remotely.
- [ ] PF-073 | phase: P9 | packet: PKT-B2 | deps: PF-072 | owner: unassigned | status: blocked | output: row-smoothing constructor | evidence: weighted kernel estimate | task: Prove the analytic row-smoothing hypothesis.
- [ ] PF-074 | phase: P10 | packet: PKT-B2 | deps: PF-051, PF-052, PF-073 | owner: unassigned | status: blocked | output: fixed-`Ls` IUC inhabitant | evidence: remote theorem and axiom check | task: Construct the factorized block trace hypothesis.
- [ ] PF-075 | phase: P12 | packet: PKT-B2 | deps: PF-040, PF-074 | owner: unassigned | status: blocked | output: uniform lattice block clustering | evidence: physical-distance estimate | task: Discharge the conditional clustering theorem.
- [ ] PF-076 | phase: P13 | packet: PKT-B3 | deps: PF-075 | owner: unassigned | status: blocked | output: observable approximation theorem | evidence: domination and integrability proof | task: Extend clustering beyond truncated slices.
- [ ] PF-077 | phase: P14 | packet: PKT-B3 | deps: PF-076 | owner: unassigned | status: blocked | output: cylinder weak-limit clustering | evidence: uniform-integrability limit theorem | task: Pass connected correlations through the cylinder limit.
- [ ] PF-078 | phase: P15 | packet: PKT-B3 | deps: PF-077 | owner: unassigned | status: blocked | output: cylinder OS4 headline | evidence: focused remote `#print axioms` | task: Publish OS4 on the constructed cylinder measure.
- [ ] PF-079 | phase: P16 | packet: PKT-B3 | deps: PF-078 | owner: reviewer | status: queued | output: Part B release review | evidence: exact-SHA CI, assurance, and source audit | task: Approve the fixed-circumference OS4 package.
- [ ] PF-080 | phase: P4 | packet: PKT-C1 | deps: BG-024 | owner: part-c-owner | status: ready | output: continuum Green convention theorem | evidence: definition-to-Fourier review | task: Freeze the physical bilinear form.
- [ ] PF-081 | phase: P5 | packet: PKT-C1 | deps: PF-080 | owner: part-c-owner | status: queued | output: flat complex DFT identities | evidence: focused remote compile | task: Verify the finite Fourier normalization.
- [ ] PF-082 | phase: P6 | packet: PKT-C1 | deps: PF-081 | owner: part-c-owner | status: queued | output: compact-support UV theorem | evidence: moving-frequency Riemann sums | task: Prove the bounded-frequency lattice limit.
- [ ] PF-083 | phase: P7 | packet: PKT-C1 | deps: PF-082 | owner: part-c-owner | status: queued | output: two-dimensional tail bound | evidence: product-tail estimate | task: Remove the compact frequency cutoff.
- [ ] PF-084 | phase: P8 | packet: PKT-C1 | deps: PF-083 | owner: part-c-owner | status: queued | output: joint Green convergence | evidence: remote `#print axioms` | task: Replace `latticeGreenBilinear_basis_tendsto_continuum`.
- [ ] PF-085 | phase: P3 | packet: PKT-C2 | deps: BG-023 | owner: part-c-owner | status: ready | output: sequence tail-reindexing lemma | evidence: focused remote compile | task: Derive eventual `a <= 1` without changing the limit.
- [ ] PF-086 | phase: P4 | packet: PKT-C2 | deps: PF-085 | owner: part-c-owner | status: queued | output: canonical CF convergence theorem | evidence: exact `IsPphi2Limit` field projection | task: Replace the canonical characteristic-function axiom.
- [ ] PF-087 | phase: P19 | packet: PKT-C3 | deps: PF-063, BG-023 | owner: unassigned | status: blocked | output: plane exponential-moment input | evidence: Part A uniform bound and lower-semicontinuity | task: Transfer the cylinder or torus moment control to coupled approximants.
- [ ] PF-088 | phase: P20 | packet: PKT-C3 | deps: PF-087 | owner: unassigned | status: blocked | output: polynomial uniform integrability | evidence: truncation and moment-tail proof | task: Control every moment used by `IsPphi2Limit`.
- [ ] PF-089 | phase: P21 | packet: PKT-C3 | deps: PF-084, PF-088 | owner: unassigned | status: blocked | output: mixed Green-form exponential moment | evidence: remote theorem check | task: Replace `continuum_exponential_moment_bound`.
- [ ] PF-090 | phase: P3 | packet: PKT-C4 | deps: BG-023, BG-033 | owner: unassigned | status: blocked | output: coupled tightness theorem | evidence: source-faithful cofinal estimates | task: Prove tightness for one UV and IR diagonal family.
- [ ] PF-091 | phase: P4 | packet: PKT-C4 | deps: PF-090 | owner: unassigned | status: blocked | output: coupled subsequence | evidence: Prokhorov and diagonal extraction | task: Select actual lattice approximants with all scale limits.
- [ ] PF-092 | phase: P21 | packet: PKT-C4 | deps: PF-086, PF-088, PF-091 | owner: unassigned | status: blocked | output: `IsPphi2Limit` inhabitant | evidence: every structure field checked | task: Package the coupled plane witness.
- [ ] PF-093 | phase: P22 | packet: PKT-C4 | deps: PF-092 | owner: unassigned | status: blocked | output: `pphi2_limit_exists` theorem | evidence: focused remote `#print axioms` | task: Replace the plane-existence axiom.
- [ ] PF-094 | phase: P17 | packet: PKT-C5 | deps: PF-079, BG-023 | owner: unassigned | status: blocked | output: phase-aware spatial clustering input | evidence: exact uniformity structure | task: State the spatial-volume limit hypothesis honestly.
- [ ] PF-095 | phase: P18 | packet: PKT-C5 | deps: PF-094 | owner: unassigned | status: blocked | output: cylinder-to-plane clustering transfer | evidence: spatial IR estimate | task: Pass fixed-circumference clustering to growing circumference.
- [ ] PF-096 | phase: P22 | packet: PKT-C5 | deps: PF-092, PF-095 | owner: unassigned | status: blocked | output: plane clustering theorem | evidence: weak-limit connected-correlation proof | task: Replace `continuum_exponential_clustering`.
- [ ] PF-097 | phase: P4 | packet: PKT-C6 | deps: BG-025 | owner: unassigned | status: blocked | output: rotated-observable lattice identity | evidence: genuine Ward derivative calculation | task: Replace the tautological lattice identity.
- [ ] PF-098 | phase: P5 | packet: PKT-C6 | deps: PF-097 | owner: unassigned | status: blocked | output: uniform rotation defect | evidence: polylogarithmic bound | task: Replace `rotation_cf_defect_polylog_bound`.
- [ ] PF-099 | phase: P23 | packet: PKT-C7 | deps: PF-084, PF-089, PF-093, PF-096, PF-098 | owner: root | status: blocked | output: plane OS package | evidence: focused remote axiom report | task: Assemble OS0 through OS4 on the coupled witness.
- [ ] PF-100 | phase: P24 | packet: PKT-C7 | deps: PF-099 | owner: root | status: blocked | output: live Bridge consumer cleanup | evidence: dependency trace | task: Remove the plane dependence on `os2_from_phi4`.
- [ ] PF-101 | phase: P25 | packet: PKT-C7 | deps: PF-100 | owner: reviewer | status: queued | output: Part C release review | evidence: exact-SHA CI, assurance, and source audit | task: Approve the plane existence and OS package.
- [ ] PF-102 | phase: P3 | packet: PKT-D0 | deps: BG-026 | owner: part-d-owner | status: blocked | output: corrected KP provenance | evidence: source SHA, license, and file hash map | task: Repair the recovered-source record.
- [ ] PF-103 | phase: P4 | packet: PKT-D0 | deps: PF-102 | owner: part-d-owner | status: blocked | output: coherent 20-file scaffold commit | evidence: complete import closure | task: Stage the generic ClusterExpansion tree as one unit.
- [ ] PF-104 | phase: P5 | packet: PKT-D0 | deps: PF-103 | owner: root | status: blocked | output: scaffold compile certificate | evidence: exact-SHA remote CI and `#print axioms` | task: Verify the generic KP, BKAR, and Schur modules.
- [ ] PF-105 | phase: P3 | packet: PKT-D1 | deps: BG-027 | owner: pfaffian-owner | status: ready | output: finite-set order isomorphism | evidence: focused remote compile | task: Reindex matching parts from an ambient finite set to its subtype.
- [ ] PF-106 | phase: P4 | packet: PKT-D1 | deps: PF-105 | owner: pfaffian-owner | status: queued | output: perfect-matching equivalence | evidence: `Finpartition.toSubtype` and inverse construction | task: Transport matchings in both directions.
- [ ] PF-107 | phase: P5 | packet: PKT-D1 | deps: PF-106 | owner: pfaffian-owner | status: queued | output: crossing-sign preservation | evidence: `Finset.card_bij` on crossing pairs | task: Preserve the Pfaffian matching sign.
- [ ] PF-108 | phase: P6 | packet: PKT-D1 | deps: PF-107 | owner: pfaffian-owner | status: queued | output: `pfOn_eq_pf_principalSubmatrix` | evidence: focused remote theorem check | task: Complete the Pfaffian bridge with the correct sum orientation.
- [ ] PF-109 | phase: P6 | packet: PKT-D2 | deps: PF-104 | owner: unassigned | status: blocked | output: continuous-spin measurable model | evidence: product Borel and finite-volume measure proof | task: Instantiate real unbounded spin configurations.
- [ ] PF-110 | phase: P7 | packet: PKT-D2 | deps: PF-108, PF-109 | owner: unassigned | status: blocked | output: finite AR/BKAR identity | evidence: forest interpolation theorem | task: Prove the block decoupling formula.
- [ ] PF-111 | phase: P8 | packet: PKT-D2 | deps: PF-110 | owner: unassigned | status: blocked | output: Schur-positive covariance interpolation | evidence: principal-minor and Schur-complement proof | task: Preserve covariance positivity along the forest path.
- [ ] PF-112 | phase: P9 | packet: PKT-D3 | deps: PF-111 | owner: unassigned | status: blocked | output: pphi2 polymer activities | evidence: finite-volume Gibbs expansion | task: Map physical blocks to the generic polymer system.
- [ ] PF-113 | phase: P10 | packet: PKT-D3 | deps: PF-112 | owner: unassigned | status: blocked | output: integrated covariance bound | evidence: `a^4` adjacent-block sum estimate | task: Prove the correctly scaled covariance input.
- [ ] PF-114 | phase: P11 | packet: PKT-D3 | deps: PF-113 | owner: unassigned | status: blocked | output: uniform activity moments | evidence: Nelson, Wick, and hypercontractivity bounds | task: Control all derivatives in the block activity.
- [ ] PF-115 | phase: P12 | packet: PKT-D3 | deps: PF-114 | owner: unassigned | status: blocked | output: coefficient-aware weak-coupling condition | evidence: explicit KP row-sum inequality | task: Define and prove the small-coupling criterion.
- [ ] PF-116 | phase: P13 | packet: PKT-D3 | deps: PF-104, PF-115 | owner: unassigned | status: blocked | output: pphi2 KP theorem | evidence: focused remote axiom report | task: Instantiate the generic KP bounds.
- [ ] PF-117 | phase: P14 | packet: PKT-D4 | deps: PF-116 | owner: unassigned | status: blocked | output: fixed-spacing boundary independence | evidence: cluster-tail estimate | task: Compare arbitrary boundary conditions.
- [ ] PF-118 | phase: P15 | packet: PKT-D4 | deps: PF-117 | owner: unassigned | status: blocked | output: continuum-uniform cluster tails | evidence: scale-independent constants | task: Preserve boundary decay along the coupled limit.
- [ ] PF-119 | phase: P23 | packet: PKT-D4 | deps: PF-093, PF-118 | owner: unassigned | status: blocked | output: common Schwinger functions | evidence: convergent cluster derivatives | task: Identify every plane subsequential moment.
- [ ] PF-120 | phase: P24 | packet: PKT-D4 | deps: PF-089, PF-119 | owner: unassigned | status: blocked | output: `pphi2_limit_unique` | evidence: moment determinacy theorem | task: Prove uniqueness of the actual coupled limit.
- [ ] PF-121 | phase: P25 | packet: PKT-D5 | deps: PF-120 | owner: unassigned | status: blocked | output: `schwinger_agreement` theorem | evidence: unique-limit identification | task: Replace the bridge axiom on the common measure.
- [ ] PF-122 | phase: P25 | packet: PKT-D5 | deps: PF-120 | owner: unassigned | status: blocked | output: positive two-point theorem | evidence: transported strict lower bound | task: Replace `pphi2_nontriviality`.
- [ ] PF-123 | phase: P25 | packet: PKT-D5 | deps: PF-120 | owner: unassigned | status: blocked | output: nonzero connected four-point theorem | evidence: transported weak-coupling torus witness | task: Replace `continuumLimit_nonGaussian`.
- [ ] PF-124 | phase: P26 | packet: PKT-D5 | deps: PF-099, PF-121, PF-122, PF-123 | owner: root | status: blocked | output: one-measure interacting headline | evidence: focused remote `#print axioms` | task: Publish the full OS and interaction theorem.
- [ ] PF-125 | phase: P27 | packet: PKT-R0 | deps: PF-064, PF-079, PF-101, PF-124 | owner: root | status: blocked | output: fresh composite branch | evidence: reviewed commit manifest | task: Assemble Parts A through D from their certified packets.
- [ ] PF-126 | phase: P28 | packet: PKT-R0 | deps: PF-125 | owner: root | status: blocked | output: green full build | evidence: exact-SHA remote CI | task: Compile the active `Pphi2` and `Common` targets.
- [ ] PF-127 | phase: P28 | packet: PKT-R0 | deps: PF-125 | owner: root | status: blocked | output: full assurance result | evidence: exact-SHA remote assurance | task: Run sorry confinement and kernel reporting.
- [ ] PF-128 | phase: P29 | packet: PKT-R0 | deps: PF-126, PF-127 | owner: root | status: blocked | output: synchronized golden report | evidence: remote generator diff | task: Commit the exact final axiom trace.
- [ ] PF-129 | phase: P30 | packet: PKT-R0 | deps: PF-128 | owner: reviewer | status: blocked | output: final mathematical audit | evidence: independent source and quantifier review | task: Verify every retained external dependency.
- [ ] PF-130 | phase: P30 | packet: PKT-R0 | deps: PF-128 | owner: root | status: blocked | output: final repository hygiene report | evidence: clean index, artifact scan, and `git diff --check` | task: Confirm local-only files and build artifacts remain excluded.
- [ ] PF-131 | phase: P31 | packet: PKT-R0 | deps: PF-129, PF-130 | owner: root | status: blocked | output: completed local ledgers | evidence: exact SHAs, run IDs, and footprints | task: Record the final Part A through D evidence.
- [ ] PF-132 | phase: P32 | packet: PKT-R0 | deps: PF-131 | owner: root | status: blocked | output: review-ready branch with no PR | evidence: fork ref and final status | task: Stop before pull-request creation.
- [x] PF-133 | phase: P10 | packet: PKT-A0R | deps: PF-007, PF-008 | owner: root | status: done | output: three-error repair patch | evidence: filtered remote error log and independent static review | task: Repair `AsymLatticeMeasure` lines 310, 375, and 421.
- [x] PF-134 | phase: P11 | packet: PKT-A0R | deps: PF-133 | owner: root | status: done | output: follow-up compiler commit `b7ebef3177da1ca870092922dc14ef1e06b71118` | evidence: clean staged diff and git commit | task: Commit the narrow lattice-measure repair.
- [ ] PF-135 | phase: P12 | packet: PKT-A0R | deps: PF-134 | owner: root | status: queued | output: updated fork branch | evidence: exact fork SHA | task: Push the follow-up compiler commit.
- [ ] PF-136 | phase: P13 | packet: PKT-A0R | deps: PF-135 | owner: root | status: queued | output: two replacement remote runs | evidence: dispatched CI and assurance IDs | task: Re-run both workflows on one exact SHA.
- [ ] PF-137 | phase: P14 | packet: PKT-A0R | deps: PF-136 | owner: root | status: queued | output: replacement CI conclusion | evidence: complete build log | task: Inspect the full remote build.
- [ ] PF-138 | phase: P14 | packet: PKT-A0R | deps: PF-136 | owner: root | status: queued | output: replacement assurance conclusion | evidence: kernel report and sorry guard | task: Inspect assurance and capture the fresh report.

### Phase map

| Phase | Items | External prerequisites | Expected artifact | Parallel width |
|---|---|---|---|---:|
| P0 | BG-001, BG-002, BG-003, BG-004, BG-005, BG-006 | repository access | literal contracts and pins | 6 |
| P1 | BG-007, BG-011, BG-012, BG-013, BG-014, BG-016, BG-030, BG-033, BG-037 | P0 contracts and readable worktrees | inventories, workflow map, and first source verdict | 9 |
| P2 | BG-008, BG-009, BG-010, BG-022, BG-023, BG-026, BG-027, BG-028, BG-029, BG-031, BG-036, PF-065, PF-066 | listed P1 outputs | theorem fronts, ownership rules, and failed-run evidence | 13 |
| P3 | BG-015, BG-017, BG-018, BG-019, BG-020, BG-021, BG-024, BG-025, BG-032, BG-034, BG-039, PF-067, PF-085, PF-090, PF-102, PF-105 | listed P2 outputs and primary sources | API maps, convention audits, ledgers, and foundation interfaces | 16 |
| P4 | BG-035, BG-038, PF-001, PF-009, PF-042, PF-046, PF-068, PF-080, PF-086, PF-091, PF-097, PF-103, PF-106 | listed P3 outputs | release gate, source map, and first implementation packets | 13 |
| P5 | BG-040, PF-002, PF-010, PF-011, PF-013, PF-028, PF-034, PF-043, PF-047, PF-054, PF-069, PF-081, PF-098, PF-104, PF-107 | listed P4 outputs | baseline freeze and first producer lemmas | 15 |
| P6 | PF-003, PF-012, PF-014, PF-029, PF-035, PF-044, PF-048, PF-055, PF-070, PF-082, PF-108, PF-109 | listed P5 outputs | commits, semantic bridges, and analytic setup | 12 |
| P7 | PF-004, PF-015, PF-020, PF-030, PF-036, PF-045, PF-049, PF-050, PF-056, PF-071, PF-083, PF-110 | listed P6 outputs and fork access | pushed baseline and first compiled frontiers | 12 |
| P8 | PF-005, PF-006, PF-016, PF-021, PF-031, PF-037, PF-051, PF-052, PF-057, PF-072, PF-084, PF-111 | listed P7 outputs and remote runners | remote jobs, bridge theorems, and first discharged inputs | 12 |
| P9 | PF-007, PF-008, PF-017, PF-018, PF-023, PF-032, PF-038, PF-053, PF-058, PF-073, PF-112 | listed P8 outputs | baseline conclusions and analytic identities | 11 |
| P10 | PF-019, PF-025, PF-033, PF-039, PF-059, PF-074, PF-113, PF-133 | listed P9 outputs | paired factorization, convergence pieces, and compiler retry patch | 8 |
| P11 | PF-022, PF-040, PF-114, PF-134 | listed P10 outputs | uniform integrability, gap theorem, moment bounds, and retry commit | 4 |
| P12 | PF-024, PF-041, PF-075, PF-115, PF-135 | listed P11 outputs | MGF convergence, reviewed gap, clustering, weak coupling, and fork update | 5 |
| P13 | PF-026, PF-076, PF-116, PF-136 | listed P12 outputs | producer package, approximation, KP instantiation, and replacement runs | 4 |
| P14 | PF-027, PF-077, PF-117, PF-137, PF-138 | listed P13 outputs | Layer A theorem, weak-limit passage, boundary result, and baseline certificates | 5 |
| P15 | PF-060, PF-078, PF-118 | listed P14 outputs | thresholded variance, cylinder clustering, and cluster tails | 3 |
| P16 | PF-061, PF-079 | listed P15 outputs | signed moment theorem and Part B release review | 2 |
| P17 | PF-062, PF-094 | listed P16 outputs | torus moment and plane spatial clustering input | 2 |
| P18 | PF-063, PF-095 | listed P17 outputs | cylinder headline and plane weak-limit clustering | 2 |
| P19 | PF-064, PF-087 | listed P18 outputs | Part A release review and plane moment producer | 2 |
| P20 | PF-088 | listed P19 outputs | plane mixed Green-form moment | 1 |
| P21 | PF-089, PF-092 | listed P20 and independent predecessor outputs | plane exponential UI and coupled diagonal sequence | 2 |
| P22 | PF-093, PF-096 | listed P21 outputs | coupled plane witness and clustering transfer | 2 |
| P23 | PF-099, PF-119 | listed P22 outputs and Part D tails | plane OS package and common Schwinger functions | 2 |
| P24 | PF-100, PF-120 | listed P23 outputs | live consumer cleanup and coupled-limit uniqueness | 2 |
| P25 | PF-101, PF-121, PF-122, PF-123 | listed P24 outputs | Part C review and one-measure interaction witnesses | 4 |
| P26 | PF-124 | listed P25 outputs | one-measure interacting headline | 1 |
| P27 | PF-125 | certified Part A through Part D outputs | fresh composite branch | 1 |
| P28 | PF-126, PF-127 | fork runner access and P27 composite | full CI and assurance results | 2 |
| P29 | PF-128 | green P28 runs | synchronized kernel report | 1 |
| P30 | PF-129, PF-130 | exact P29 source set | mathematical and hygiene audits | 2 |
| P31 | PF-131 | approved P30 audits | complete evidence ledgers | 1 |
| P32 | PF-132 | final fork push | review-ready branch without a PR | 1 |

Critical path:

```text
BG-038 -> PF-013 -> PF-014 -> PF-015 -> PF-016 -> PF-017 -> PF-019
  -> PF-022 -> PF-024 -> PF-026 -> PF-027 -> PF-060 -> PF-061
  -> PF-062 -> PF-063 -> PF-064 -> PF-125
PF-016 -> PF-018 -> PF-019
PF-020 -> PF-021 -> PF-022
PF-021 -> PF-023 -> PF-025 -> PF-026

PF-007 -> PF-133 -> PF-134 -> PF-135 -> PF-136 -> PF-137 -> PF-060
PF-008 -> PF-133 -> PF-134 -> PF-135 -> PF-136 -> PF-138 -> PF-060

PF-072 -> PF-073 -> PF-074 -> PF-075 -> PF-076 -> PF-077 -> PF-078
  -> PF-079 -> PF-125
PF-040 -> PF-075
PF-051 -> PF-074
PF-052 -> PF-074

PF-063 -> PF-087 -> PF-088 -> PF-092 -> PF-093 -> PF-099 -> PF-100
  -> PF-101 -> PF-125
PF-084 -> PF-089 -> PF-099
PF-079 -> PF-094 -> PF-095 -> PF-096 -> PF-099
PF-097 -> PF-098 -> PF-099

BG-026 -> PF-102 -> PF-103 -> PF-104 -> PF-109 -> PF-110 -> PF-111
  -> PF-112 -> PF-113 -> PF-114 -> PF-115 -> PF-116 -> PF-117
  -> PF-118 -> PF-119 -> PF-120 -> PF-121 -> PF-124 -> PF-125
BG-027 -> PF-105 -> PF-106 -> PF-107 -> PF-108 -> PF-110
PF-120 -> PF-122 -> PF-124
PF-120 -> PF-123 -> PF-124

PF-125 -> PF-126 -> PF-128 -> PF-129 -> PF-131 -> PF-132
PF-125 -> PF-127 -> PF-128 -> PF-130 -> PF-131 -> PF-132
```

### Execution packets

- PKT-00 | items: BG-001 to BG-006, BG-016 | prerequisites: none | files: goal files, README, toolchain, manifest | acceptance: bounded reads and worktree resolution | handoff: frozen literal contracts | status: done | lead: root | subagents: contract splitting | difficulty: low | priority: critical.
- PKT-01 | items: BG-007 to BG-010, BG-015, BG-037 | prerequisites: PKT-00 | files: live AsymTorus consumers, audit generator | acceptance: declaration trace and source scan | handoff: current axiom DAG | status: done | lead: root | subagents: Layer A, B2, evidence | difficulty: medium | priority: critical.
- PKT-02 | items: BG-011 to BG-014, BG-029, BG-036, BG-039 | prerequisites: PKT-00 | files: all active worktrees | acceptance: status, merge-base, ownership audit | handoff: safe integration policy | status: done | lead: root | subagents: one worktree each | difficulty: medium | priority: high.
- PKT-03 | items: BG-030 to BG-032 | prerequisites: PKT-00 | files: workflows and local ledger | acceptance: exact run conclusions and ledger patch | handoff: failed-baseline evidence and current ledger | status: done | lead: root | subagents: log filtering | difficulty: low | priority: critical.
- PKT-04 | items: BG-034, BG-035, BG-040 | prerequisites: PKT-01, PKT-03 | files: `LEAN_PROOF_PLAN.md` | acceptance: all fatal and major findings encoded | handoff: frozen plan | status: active | lead: root | subagents: contract and phase review | difficulty: medium | priority: critical.
- PKT-AX | items: BG-021 | prerequisites: PKT-01 | files: `AsymUniformTiltedMoment.lean`, DDJ source modules | acceptance: exact conditional pressure interface | handoff: separate alternative lane | status: done | lead: ddj-frontier | subagents: pressure source review | difficulty: medium | priority: low.
- PKT-A0 | items: PF-001 to PF-008 | prerequisites: PKT-03 | files: compiler-repair files, workflows, and baseline run records | acceptance: exact-SHA CI and assurance results recorded for `7cf129f`, including the localized failure and passing sorry guard | handoff: failed-baseline evidence and reviewed retry target | status: done | lead: root | subagents: failed-target review | difficulty: medium | priority: critical.
- PKT-A0R | items: PF-133 to PF-138 | prerequisites: PKT-A0 | files: `AsymLatticeMeasure.lean`, `LEAN_PROOF_PLAN.md`, and replacement run records | acceptance: pushed follow-up SHA, green exact-SHA CI and assurance, checked kernel report, passing sorry guard, and no new source holes | handoff: certified Part A execution baseline | status: active | lead: root | subagents: repair review and log filtering | difficulty: medium | priority: critical.
- PKT-A1 | items: BG-017, BG-038, PF-009 to PF-012 | prerequisites: PKT-01 | files: new `AsymWickGibbsDensity.lean`, Wick adapter | acceptance: focused remote compile and semantic review | handoff: finite ferromagnetic Gibbs density | status: ready | lead: layer-a-density | subagents: energy, density, measurability | difficulty: high | priority: high.
- PKT-A2 | items: PF-013 to PF-019 | prerequisites: PKT-A1 and source pages | files: pphi2 Layer A adapter and lee-yang-local helpers | acceptance: semantic paired-factor certificate | handoff: finite Newman data | status: blocked | lead: unassigned | subagents: shared spin, roots, factor identities | difficulty: research | priority: critical.
- PKT-A3 | items: PF-020 to PF-027 | prerequisites: PKT-A2 | files: `AsymInteractingLeeYang.lean`, `AsymExpMomentDischarge.lean` | acceptance: focused CI and axiom-free Layer A output | handoff: replaced Layer A axiom | status: blocked | lead: unassigned | subagents: weak convergence, UI, variance | difficulty: research | priority: critical.
- PKT-A4 | items: BG-018, PF-028 to PF-033 | prerequisites: source-normalization map | files: `AsymInfraredBound.lean`, reflection-positive adapters | acceptance: focused CI, exact FSS footprint | handoff: proved high-mode input | status: blocked | lead: unassigned | subagents: RP, chessboard, Fourier normalization | difficulty: research | priority: critical.
- PKT-A5 | items: BG-019, PF-034 to PF-041 | prerequisites: primary spectral map | files: transfer and slice-family modules | acceptance: fixed-`Ls` uniform-gap certificate | handoff: one physical contraction rate | status: blocked | lead: unassigned | subagents: forms, compactness, spectrum | difficulty: research | priority: critical.
- PKT-A6 | items: BG-020, PF-042 to PF-045 | prerequisites: existing GroundBridge APIs | files: new `AsymTraceSplit.lean` and wrapper | acceptance: focused remote compile | handoff: fixed-parameter trace dictionary | status: ready | lead: bridge-owner | subagents: residual and path dictionary | difficulty: medium | priority: high.
- PKT-A7 | items: PF-046 to PF-053 | prerequisites: PKT-A6 and PKT-A5 | files: trace bridge and slice-family estimates | acceptance: two focused axiom reports | handoff: diagonal and residual discharges | status: ready for algebra, blocked for uniform analysis | lead: unassigned | subagents: numerator, denominator, IUC | difficulty: research | priority: critical.
- PKT-A8 | items: PF-054 to PF-059 | prerequisites: source page map | files: `AsymB5bSingleSlice.lean` and ground-state adapters | acceptance: focused axiom report and scaling review | handoff: ground/free comparison | status: blocked | lead: unassigned | subagents: marginal, Nelson, covariance | difficulty: research | priority: critical.
- PKT-A9 | items: PF-060 to PF-064 | prerequisites: PKT-A0R, PKT-A3 to PKT-A8 | files: variance assembly, covariance positivity, continuum limit | acceptance: exact Part A kernel report and independent audit | handoff: complete Part A branch | status: blocked | lead: root | subagents: consumer trace and release review | difficulty: high | priority: critical.
- PKT-B0 | items: BG-022 | prerequisites: PKT-02 | files: Part B conditional consumers | acceptance: complete OS4 graph | handoff: Part B ownership map | status: done | lead: part-b-contract | subagents: kernel and weak-limit routes | difficulty: medium | priority: high.
- PKT-B1 | items: PF-065 to PF-072 | prerequisites: PKT-B0 | files: seven modified and three new Part B modules | acceptance: staged remote checks per source group, then root import build | handoff: certified conditional kernel pipeline | status: ready | lead: part-b-owner | subagents: semigroup, remainder, row smoothing | difficulty: high | priority: high.
- PKT-B2 | items: PF-073 to PF-075 | prerequisites: PKT-B1, PKT-A5, PKT-A7 | files: row smoothing, IUC, block clustering | acceptance: model-specific IUC inhabitant and clustering footprint | handoff: uniform lattice OS4 input | status: blocked | lead: unassigned | subagents: smoothing, denominator, geometry | difficulty: research | priority: critical.
- PKT-B3 | items: PF-076 to PF-079 | prerequisites: PKT-B2 | files: observable approximation and CylinderOS4 modules | acceptance: exact-SHA CI, assurance, OS4 axiom report | handoff: complete Part B branch | status: blocked | lead: unassigned | subagents: truncation and weak limit | difficulty: high | priority: critical.
- PKT-C0 | items: BG-023 to BG-025, BG-033 | prerequisites: PKT-02 | files: coupled-limit, Green, Ward declarations and sources | acceptance: convention and citation audit | handoff: sound Part C interfaces | status: done | lead: part-cd-contract | subagents: Green, rotation, existence sources | difficulty: medium | priority: critical.
- PKT-C1 | items: PF-080 to PF-084 | prerequisites: PKT-C0 | files: EmbeddedCovariance, FlatComplexDFT, FlatComplexUV, FlatUVLimit, PropagatorConvergence | acceptance: focused checks and full bilinear axiom report | handoff: joint Green convergence | status: ready | lead: part-c-owner | subagents: DFT, compact UV, tails | difficulty: high | priority: high.
- PKT-C2 | items: PF-085, PF-086 | prerequisites: PKT-C0 | files: AxiomInheritance and sequence helpers | acceptance: focused remote compile | handoff: canonical CF theorem | status: ready | lead: part-c-owner | subagents: tail reindexing | difficulty: medium | priority: high.
- PKT-C3 | items: PF-087 to PF-089 | prerequisites: PKT-A9, PKT-C1 | files: PlaneMomentProducer, PlanePolynomialUI, inheritance | acceptance: moment and UI axiom report | handoff: plane exponential-moment theorem | status: blocked | lead: unassigned | subagents: truncation, UI, Green control | difficulty: research | priority: critical.
- PKT-C4 | items: PF-090 to PF-093 | prerequisites: PKT-C2, PKT-C3 | files: Tightness, PlaneExistence, Convergence | acceptance: every `IsPphi2Limit` field and remote certificate | handoff: actual coupled plane witness | status: blocked | lead: unassigned | subagents: tightness, diagonal sequence, packaging | difficulty: research | priority: critical.
- PKT-C5 | items: PF-094 to PF-096 | prerequisites: PKT-B3, PKT-C4 | files: plane translation and clustering modules | acceptance: phase-aware spatial-uniform clustering theorem | handoff: plane OS4 input | status: blocked | lead: unassigned | subagents: spatial IR and weak limit | difficulty: research | priority: critical.
- PKT-C6 | items: PF-097, PF-098 | prerequisites: PKT-C0 | files: `OS2_WardIdentity.lean` | acceptance: genuine rotated-observable bound | handoff: axiom-free rotation defect | status: blocked | lead: unassigned | subagents: Ward identity and estimates | difficulty: research | priority: high.
- PKT-C7 | items: PF-099 to PF-101 | prerequisites: PKT-C1, PKT-C3 to PKT-C6 | files: Main, Bridge, plane OS assembly, audit | acceptance: exact-SHA CI, assurance, plane headline report | handoff: complete Part C branch | status: blocked | lead: root | subagents: consumer cleanup and source review | difficulty: high | priority: critical.
- PKT-D0 | items: BG-026, BG-028, PF-102 to PF-104 | prerequisites: PKT-02 | files: complete 20-file ClusterExpansion tree, imports, provenance | acceptance: source hash, license, remote build, axiom report | handoff: certified generic scaffold | status: blocked on provenance | lead: part-d-owner | subagents: provenance, imports, CI | difficulty: high | priority: high.
- PKT-D1 | items: BG-027, PF-105 to PF-108 | prerequisites: current Pfaffian APIs | files: Pfaffian Basic or dedicated bridge module | acceptance: focused remote compile and sign audit | handoff: principal-submatrix Pfaffian theorem | status: ready | lead: pfaffian-owner | subagents: partition equivalence and crossings | difficulty: high | priority: high.
- PKT-D2 | items: PF-109 to PF-111 | prerequisites: PKT-D0, PKT-D1 | files: ContinuousConfig, Measure, BKAR, SchurProduct | acceptance: focused remote theorem suite | handoff: continuous-spin forest identity | status: blocked | lead: unassigned | subagents: measurability, forest algebra, PSD | difficulty: research | priority: critical.
- PKT-D3 | items: PF-112 to PF-116 | prerequisites: PKT-D2 | files: pphi2 activity and KP instantiation modules | acceptance: explicit coefficient-aware row-sum theorem | handoff: uniform pphi2 KP control | status: blocked | lead: unassigned | subagents: covariance, Nelson, activities | difficulty: research | priority: critical.
- PKT-D4 | items: PF-117 to PF-120 | prerequisites: PKT-D3, PKT-C4 | files: boundary, coupled uniqueness, moment bridge | acceptance: exact `pphi2_limit_unique` footprint | handoff: unique coupled plane measure | status: blocked | lead: unassigned | subagents: tails, moments, determinacy | difficulty: research | priority: critical.
- PKT-D5 | items: PF-121 to PF-124 | prerequisites: PKT-D4, PKT-C7 | files: Bridge, Convergence, Main | acceptance: one-measure headline and focused axiom report | handoff: complete Part D branch | status: blocked | lead: root | subagents: agreement, S2, connected four-point | difficulty: high | priority: critical.
- PKT-R0 | items: PF-125 to PF-132 | prerequisites: PKT-A9, PKT-B3, PKT-C7, PKT-D5 | files: fresh composite, audit, ledgers, status docs | acceptance: full CI, assurance, kernel sync, hygiene, independent source review | handoff: review-ready fork branch | status: blocked | lead: root | subagents: integration, evidence, release audit | difficulty: high | priority: critical.
