# Euclidean QFT Formulation Layer

Technical reference for the shared formulation-layer interfaces in
`Common/QFT/Euclidean/`.

For motivation and long-term design goals, see
[`foundational-roadmap.md`](foundational-roadmap.md).

## Overview

The P(Phi)\_2 construction produces a probability measure on S'(R^2) satisfying
the Osterwalder-Schrader axioms. But a probability measure on a configuration
space is not the same thing as a general QFT: gauge theories, fermionic
theories, and the original OS axioms themselves operate at different levels of
abstraction. The formulation layer makes these distinctions explicit in Lean so
that:

- concrete measure-based constructions are not silently identified with general
  QFT,
- the mathematical content required at each bridge (measurability, moment
  finiteness, continuity, growth bounds) stays visible, and
- different theories can be compared at the appropriate level (Schwinger data,
  not necessarily measure equality).

All definitions live in the `Common.QFT.Euclidean` namespace. The structures
are universe-polymorphic (`uSpace`, `uTest`, `uComplex`, `uNPoint`, `uConfig`)
to allow composition across different concrete type universes.

## Test-function infrastructure

Two levels of test-function data are available, depending on how much structure
a model needs.

### `Formulation` (base structure)

Minimal one-point data shared by all Euclidean formulations:

```lean
structure Formulation where
  SpaceTime            : Type uSpace
  TestFunction         : Type uTest
  ComplexTestFunction  : Type uComplex
  positiveTimeTestFunctions : Set TestFunction
```

No algebraic or topological structure is required. This is enough for
measure-level and simple-tensor models. Provides
`Formulation.PositiveTimeTestFunction` as a subtype.

### `SchwingerFormulation` (extends `Formulation`)

Adds linear and topological infrastructure needed for genuine distributional
Schwinger functions:

- `AddCommGroup`, `Module`, `TopologicalSpace`, `IsTopologicalAddGroup`,
  `ContinuousSMul` instances on `TestFunction` (over `ℝ`) and
  `ComplexTestFunction` (over `ℂ`)
- `NPointTestFunction : ℕ → Type` with matching instances (over `ℂ`)
- `realToComplex : TestFunction → ComplexTestFunction` with proofs that it is
  additive, `ℝ`-semilinear, and continuous
- `positiveTimeSubmodule : Submodule ℝ TestFunction` with a proof that its
  carrier equals `positiveTimeTestFunctions`

All bundled instances are registered as `attribute [instance]`.

## Model structures

The models are **not** linearly ordered. They form a diamond-shaped dependency
graph based on what data they carry:

```
              GeneratingFunctionalModel
                  (Z : TestFun -> C)
                        |
         +--------------+--------------+
         |                             |
   MeasureModel <--- extends ---> PairingMeasureModel
   (Z + mu + pairing)             (mu + pairing)
                                       |
                              MeasureToTensorBridge
                                       |
                             TensorSchwingerModel
                             (S_n on simple tensors)
                                       |
                          TensorToDistributionalBridge
                                       |
                         DistributionalSchwingerModel
                         (S_n on n-point test spaces)
                                       |
                              ReconstructionInput
                                       |
                                 Wightman data
```

Horizontal lines indicate structure inheritance (`extends`). Vertical lines
indicate bridges (separate structures with compatibility proofs).

### `GeneratingFunctionalModel F`

A generating functional without any underlying measure.

```lean
structure GeneratingFunctionalModel (F : Formulation) where
  generatingFunctional        : F.TestFunction → ℂ
  complexGeneratingFunctional : F.ComplexTestFunction → ℂ
```

Some Euclidean theories (e.g., gauge theories via lattice characteristic
functionals) are naturally presented at this level even when no positive measure
model exists.

### `PairingMeasureModel F FieldConfig`

A probability measure with an evaluation pairing against real test functions.

```lean
structure PairingMeasureModel (F : Formulation) (FieldConfig : Type uConfig) where
  instMeasurableSpaceFieldConfig : MeasurableSpace FieldConfig
  measure       : Measure FieldConfig      -- uses instMeasurableSpaceFieldConfig
  isProbability : IsProbabilityMeasure measure
  pairing       : FieldConfig → F.TestFunction → ℝ
```

### `MeasureModel F FieldConfig`

The most concrete layer. Combines both of the above via multiple inheritance:

```lean
structure MeasureModel (F : Formulation) (FieldConfig : Type uConfig)
    extends GeneratingFunctionalModel F,
            PairingMeasureModel F FieldConfig
```

This is the Glimm-Jaffe/Nelson interface used by P(Phi)\_2: a probability
measure on S'(R^2) together with generating functionals and the evaluation
pairing.

### `TensorSchwingerModel F`

Schwinger functions on simple tensors f\_1 (x) ... (x) f\_n, encoded as tuples
of one-point test functions:

```lean
structure TensorSchwingerModel (F : Formulation) where
  schwinger : (n : ℕ) → (Fin n → F.TestFunction) → ℂ
```

This is strictly weaker than a genuine OS Schwinger theory on n-point test
function spaces. Has an `@[ext]` lemma.

### `DistributionalSchwingerModel F`

Genuine n-point Schwinger functions as linear functionals on n-point test
function spaces. Requires `SchwingerFormulation`:

```lean
structure DistributionalSchwingerModel (F : SchwingerFormulation) where
  tensorLift          : (n : ℕ) → (Fin n → F.TestFunction) → F.NPointTestFunction n
  schwinger           : (n : ℕ) → F.NPointTestFunction n →ₗ[ℂ] ℂ
  schwingerContinuous : ∀ n, Continuous (schwinger n)
```

Note: `schwinger n` is a `→ₗ[ℂ]` (linear map) rather than a `→L[ℂ]`
(continuous linear map). Continuity is carried as a separate proof in
`schwingerContinuous`. This avoids forcing downstream code to bundle the
topology into the map at definition time.

## Bridges

Bridges connect layers that are not related by inheritance. Each bridge is a
separate structure carrying a compatibility proof. They are not coercions
because the mathematical content at each step is nontrivial.

### `MeasureToTensorBridge F M`

Connects a `PairingMeasureModel` to a `TensorSchwingerModel`:

```lean
structure MeasureToTensorBridge (F : Formulation)
    {FieldConfig : Type uConfig} (M : PairingMeasureModel F FieldConfig) where
  tensorSchwinger : TensorSchwingerModel F
  compatible :
    ∀ (n : ℕ) (f : Fin n → F.TestFunction),
      tensorSchwinger.schwinger n f =
        ∫ ω, ∏ i, (M.pairing ω (f i) : ℂ) ∂M.measure
```

**No generic constructor is provided.** Measurability and integrability of the
moment observables are genuine mathematical content that must be proved in each
concrete theory. The `compatible` field records the integral formula; it does
not hide the proof obligations.

### `TensorToDistributionalBridge F T`

Connects a `TensorSchwingerModel` to a `DistributionalSchwingerModel`. This is
where continuity and extension from simple tensors to the full n-point test
function space must be proved:

```lean
structure TensorToDistributionalBridge (F : SchwingerFormulation)
    (T : TensorSchwingerModel F.toFormulation) where
  distributionalSchwinger : DistributionalSchwingerModel F
  compatible :
    ∀ (n : ℕ) (f : Fin n → F.TestFunction),
      distributionalSchwinger.schwinger n
          (distributionalSchwinger.tensorLift n f) =
        T.schwinger n f
```

### Current status

P(Phi)\_2 is connected through `MeasureToTensorBridge`. The
`TensorToDistributionalBridge` and reconstruction layers are scaffolded but not
yet instantiated for any concrete theory.

## Reconstruction

There are two parallel interfaces for reconstruction, at different levels of
generality.

### Formulation-level (`Formulations.lean`)

Tied to the `DistributionalSchwingerModel` type:

- **`ReconstructionHypothesis F`** — an abbreviation for
  `DistributionalSchwingerModel F → Prop`. The specific analytic condition
  (e.g., OS 1975 linear growth) appears as a named predicate, not an anonymous
  `Prop`.
- **`ReconstructionInput F Hypothesis`** — bundles a
  `DistributionalSchwingerModel` together with a proof that it satisfies the
  hypothesis.

Use these when working within a fixed `SchwingerFormulation` and you have
distributional Schwinger data in hand.

### Backend-independent (`ReconstructionInterfaces.lean`)

Fully parametric type classes that do not depend on `Formulation`,
`SchwingerFormulation`, or any specific library's OS/Wightman definitions:

- **`PackagedSchwingerFunctionModel Params SchwingerFamily params`** —
  parameter-indexed Schwinger data (e.g., indexed by coupling and mass).
- **`ReconstructionLinearGrowthModel`** — records the linear-growth hypothesis
  explicitly, factored through a chosen `OSPackage` type, with a proof that the
  OS package's Schwinger data matches the current `SchwingerFamily`. Provides
  `matching_package` for an existential view.
- **`WightmanReconstructionModel`** — the reconstruction rule itself:
  `∀ OS, LinearGrowth OS → ∃ Wfn, WickRotationPair OS Wfn`.
- **`wightmanExistsOfLinearGrowthAndReconstruction`** — the abstract composition
  theorem: matching linear-growth data + reconstruction rule → Wightman data.

Use these when you want to state reconstruction results that are independent of
any particular Euclidean formalization backend.

The two levels are meant to compose: a concrete theory provides
`DistributionalSchwingerModel` data (formulation-level), packages it into a
`PackagedSchwingerFunctionModel` (backend-independent), and then applies a
reconstruction rule.

## Worked example: P(Phi)\_2

The adapter in `Pphi2/FormulationAdapter.lean` shows how a concrete theory plugs
into the hierarchy.

### Step 1: Define the formulation

```lean
def pphi2Formulation : Formulation where
  SpaceTime := SpaceTime2                        -- EuclideanSpace ℝ (Fin 2)
  TestFunction := TestFunction2                   -- SchwartzMap SpaceTime2 ℝ
  ComplexTestFunction := TestFunction2ℂ           -- SchwartzMap SpaceTime2 ℂ
  positiveTimeTestFunctions := positiveTimeSubmodule2.carrier
```

### Step 2: Build a MeasureModel from any P(Phi)\_2 probability measure

```lean
def pphi2MeasureModel
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] :
    MeasureModel pphi2Formulation FieldConfig2 where
  generatingFunctional := generatingFunctional μ
  complexGeneratingFunctional := generatingFunctionalℂ μ
  instMeasurableSpaceFieldConfig := instMeasurableSpaceConfiguration
  measure := μ
  isProbability := inferInstance
  pairing := distribPairing
```

### Step 3: Build the tensor Schwinger model and bridge

```lean
def pphi2TensorSchwingerModel
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (hMoment : ∀ (n : ℕ) (f : Fin n → TestFunction2),
      Integrable (fun ω : FieldConfig2 => ∏ i, (ω (f i) : ℂ)) μ) :
    TensorSchwingerModel pphi2Formulation where
  schwinger _n f := ∫ ω : FieldConfig2, ∏ i, (ω (f i) : ℂ) ∂μ

def pphi2MeasureToTensorBridge
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (hMoment : ∀ (n : ℕ) (f : Fin n → TestFunction2),
      Integrable (fun ω : FieldConfig2 => ∏ i, (ω (f i) : ℂ)) μ) :
    MeasureToTensorBridge pphi2Formulation (pphi2PairingMeasureModel μ) where
  tensorSchwinger := pphi2TensorSchwingerModel μ hMoment
  compatible := by intro _n f; rfl
```

The `compatible` proof is `rfl` because the tensor Schwinger model is defined
directly as the integral formula. In a theory where the Schwinger functions are
constructed differently (e.g., via analytic continuation or a separate moment
package), this proof would carry real content.

### What is not yet connected

- **`SchwingerFormulation` instance** — requires bundling the Schwartz topology
  and n-point test function spaces explicitly
- **`TensorToDistributionalBridge`** — requires proving continuity of the moment
  functionals and extending from simple tensors
- **`ReconstructionInput`** — requires identifying which growth hypothesis is
  satisfied and connecting to an OS reconstruction backend

## File map

```
Common/QFT/Euclidean/
  Formulations.lean              -- Formulation, SchwingerFormulation, all model
                                    structures, bridge structures,
                                    ReconstructionHypothesis/Input
  ReconstructionInterfaces.lean  -- Backend-independent type classes:
                                    PackagedSchwingerFunctionModel,
                                    ReconstructionLinearGrowthModel,
                                    WightmanReconstructionModel

Pphi2/
  FormulationAdapter.lean        -- pphi2Formulation, pphi2MeasureModel,
                                    pphi2TensorSchwingerModel,
                                    pphi2MeasureToTensorBridge

docs/
  foundational-roadmap.md        -- Motivation and long-term design goals
```
