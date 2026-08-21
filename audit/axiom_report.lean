/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2

/-!
# Kernel axiom certificate generator for pphi2 Part A

Runs `#print axioms` on Part A's headline and regression targets. The output
is the kernel-authoritative axiom set for this list: anything absent from
the trace cannot have leaked through the printed targets.

`main_results` (5) from `formalization.yaml`:

* `Pphi2.pphi2_existence` — ∃ μ on S'(ℝ²) satisfying OS0–OS4 (conditional).
* `Pphi2.pphi2_main` — a P(Φ)₂ continuum-limit measure satisfies the OS bundle.
* `Pphi2.pphi2_nonGaussianity` — u₄ ≠ 0 (rests on `continuumLimit_nonGaussian`).
* `Pphi2.pphi2_nontrivial` — S₂(f,f) > 0 (rests on `pphi2_nontriviality`).
* `Pphi2.cylinderIso_OS_of_RP_OS2`: quartic cylinder OS0–OS3 assembly;
  RP and OS2 are proved internally. Its non-kernel dependencies are the upstream
  axiom `GaussianField.embed_l2_uniform_bound` and the Pphi2 project axiom
  `Pphi2.asymInteracting_expMoment_volume_uniform`.

Secondary regression targets (not in `formalization.yaml`):

* `Pphi2.pphi2_exists_os_and_massParameter_positive` — the variant
  carrying the (input) mass-parameter positivity; included here as a
  regression check, not as a headline result.
* `Pphi2.asymInteractingVariance_le_freeVariance_Lt_uniform` — the
  Layer-B2 torus statement converted from axiom to theorem in Piece 5.
* `Pphi2.asymInteracting_expMoment_volume_uniform_proof` — the Layer-C
  assembly theorem consuming Layer A and Layer B2 (since 2026-07-13 in
  `AsymSignedSplit.lean`, split-seminorm form).
* `Pphi2.asymInteracting_expMoment_of_signed` — the signed-split recovery
  lemma (sole direct consumer of the sign-restricted Layer A axiom).

`pphi2_limit_unique` and `pphi2_interacting_qft_exists` are absent and are
not printed.

This generator prints headline theorems and the four named Layer-B2/C
regression targets. Finite source-tilt / DDJ plumbing is not a kernel
certificate and is not printed.

**Usage**:

```
lake env lean audit/axiom_report.lean > audit/axiom-report.txt
```

The committed `audit/axiom-report.txt` is the **golden trace**; CI diffs the
fresh run against it (when wired). The two-file split is deliberate:
generator vs. golden output, with the underscore/hyphen difference in the
filename per the hub convention. Regenerate the golden only from a successful
remote build of this branch.
-/

#print axioms Pphi2.pphi2_existence
#print axioms Pphi2.pphi2_main
#print axioms Pphi2.pphi2_nonGaussianity
#print axioms Pphi2.pphi2_nontrivial
#print axioms Pphi2.cylinderIso_OS_of_RP_OS2
#print axioms Pphi2.pphi2_exists_os_and_massParameter_positive
#print axioms Pphi2.asymInteractingVariance_le_freeVariance_Lt_uniform
#print axioms Pphi2.asymInteracting_expMoment_volume_uniform_proof
#print axioms Pphi2.asymInteracting_expMoment_of_signed
