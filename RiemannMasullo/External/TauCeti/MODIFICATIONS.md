# Modifications

Changes to the Tau Ceti sources at `8794ab329bb60340fa690a2902cf995f0571721b`,
as required by section 4(b) of the Apache License 2.0.

Each Lean file keeps its original copyright, license and author header and adds a
notice with the source path, commit and pointer to this document. The `module`
headers and `public section` markers are carried over. Imports of retained Tau Ceti
modules use the vendored paths, and the upstream `TauCeti` namespace becomes
`RiemannMasullo.External.TauCeti`. Declaration names within each namespace and the
retained proof bodies are as upstream.

## `Analysis/Normed/Group/LocallyBounded.lean`

- Omit the `GeneralDomain` section, which proves
  `isLocallyBoundedOn_of_isCompact_closure_range`, and drop its
  `Mathlib.Topology.CompactOpen` import.
- Trim the module docstring to the retained predicate and API and update the declaration
  references.

## `Analysis/Complex/Conformal/NormalFamilies.lean`

- Retain the closed-ball helper and the chain of estimates through
  `IsLocallyBoundedOn.equicontinuousOn`. Omit the separate `LipschitzOnWith` form
  `lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le`, the Cauchy kernel
  estimate `norm_inv_smul_sub_inv_smul_le`, and the derivative-family results
  `IsLocallyBoundedOn.deriv` and `IsLocallyBoundedOn.equicontinuousOn_deriv`.
- Drop `Mathlib.Topology.MetricSpace.Lipschitz`, which supplied the omitted
  `LipschitzOnWith` form.
- Trim the module docstring to the retained estimates and update its declaration and file
  references.

## `Topology/ContinuousMap/Ascoli.lean`

- Retain the section variables and
  `ArzelaAscoli.isCompact_closure_range_of_equicontinuous`, with its original
  namespace and full declaration name. The library signature comparison
  verifies that this name is a new declaration.
- Retain only the `Mathlib.Topology.UniformSpace.Ascoli` import and trim the module
  docstring to the retained result. The other compact-open results, approximation
  lemmas and periodic and Lipschitz compactness estimates are outside this excerpt.
  Neither `TauCeti.Topology.UniformSpace.Ascoli` nor `TauCeti.Algebra.Order.Floor.Ring`
  is needed.

## `Analysis/Complex/Conformal/Montel/Precompact.lean`

- Omit `isCompact_closure_range_iff_isLocallyBoundedOn` and update the module
  docstring to describe the retained implication and refer to the vendored modules.
- Update the `montel` reference in the retained declaration's docstring.

## `Analysis/Complex/Conformal/Montel/Basic.lean`

- Update the module docstring to describe the vendored compactness result and omit the
  reference to the unvendored Vitali module.

## Runge approximation: `Analysis/Complex/Runge/Approximation.lean` and its import closure

The 97 files listed after the Montel excerpt in `SOURCE_MAP.json` are whole upstream files at
the same commit. Each receives only the changes described at the top of this document:

- the notice after the upstream header;
- the module prefix `TauCeti.` in imports becomes `RiemannMasullo.External.TauCeti.`;
- every `namespace TauCeti`, `namespace TauCeti.Real`, `end …` and `open TauCeti` command, every
  qualified reference `TauCeti.x` in proofs and statements, and every such reference in
  docstrings and comments, uses `RiemannMasullo.External.TauCeti` in place of `TauCeti`. Upstream
  file paths `TauCeti/…` in docstrings are unchanged, and lines lengthened by the rename are not
  rewrapped.

- Port to Lean v4.36.0 and this project's Mathlib (`fc4f59e5`): in the 22 files below, the
  edits of upstream commit
  [`e0e414ce57`](https://github.com/TauCetiProject/TauCeti/commit/e0e414ce57522ba17560057ad0d7f2edab91bf0c)
  (Tau Ceti #44275, "bump Mathlib to v4.37.0-rc1 and replace numeric projections") are undone.
  That commit is the only upstream change to these files between its parent
  [`aa3cfad`](https://github.com/TauCetiProject/TauCeti/tree/aa3cfad1274c06cff25f2b58848498b3c3f68d0f)
  and the pinned commit, so their text is upstream's at `aa3cfad`, which upstream builds with
  Lean v4.36.0 and Mathlib `fc4f59e5`. Its edits use names that this Mathlib does not have yet
  (`continuous_subtypeVal`, `ContinuousLinearEquiv.ofContinuousLinearMap`, `exp_natCast_mul`, …).
  The files: `Analysis/Calculus/BumpFunction/Cutoff.lean`, `Analysis/Calculus/ContDiff/Bounds.lean`,
  `Analysis/Calculus/SecondDerivative.lean`, `Analysis/Complex/HolomorphicFunctions/Basic.lean`,
  `Analysis/Complex/PolynomialHull/Basic.lean`, `Analysis/Complex/Runge/Hull.lean`,
  `Analysis/Complex/Runge/SimpleFraction.lean`, `Analysis/SpecialFunctions/Exp/Bounds.lean`,
  `Geometry/Manifold/Connected.lean`, `LinearAlgebra/Complex/Module.lean`,
  `MeasureTheory/Function/Lp/Norm.lean`, `MeasureTheory/Function/LpSeminorm/AddMeasure.lean`,
  `MeasureTheory/MeasurableSpace/Metric.lean`, `MeasureTheory/Measure/OpenPos.lean`,
  `Topology/Algebra/Module/Equiv/SMul.lean`, `Topology/Compactness/Compact.lean`,
  `Topology/ConnectedComponents.lean`, `Topology/FilledHull.lean`, `Topology/Homotopy/Path.lean`,
  `Topology/MetricSpace/Holder.lean`, `Topology/PathComponent.lean`, `Topology/UnitInterval.lean`.
  Their `upstream_sha256` in `SOURCE_MAP.json` is that of the pinned commit.

Apart from that port, no declaration name (within its namespace), statement, proof or option is
changed, and nothing is omitted.
Declarations that upstream puts in Mathlib namespaces or in `_root_` keep them.
