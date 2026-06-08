# Non-Degenerate Kernel A+ Formalization Status

This folder contains the A+ audit surface for the v22 manuscript:

`Non-Degenerate Construction and the Kernel of Admissibility`

The audit harness is intentionally explicit about the boundary between closed
Lean consequence/projection rows and residual gates.  The current ledger reports
final A+ closure for the v22 theorem spine.  In particular, the formal surface
records fixed-domain uniqueness of the admissibility kernel and non-derivability
from below: no same-domain, governance-equivalent construction is available
beneath the kernel.

## Audit Command

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-minimal-conditions-a-plus-audit.ps1
```

The runner checks the eight canonical audit files, scans the kernel-paper audit
surface for live `axiom`, `unsafe`, `sorry`, or `admit`, builds
`MaleyLean.Papers.NonDegenerateConstructionAndKernelOfAdmissibility`, and runs
the focused Lean audit files.

## Current Mechanical Posture

The progress tuple exported by
`kernelAPlusCurrentProgressTuple` is:

```text
("Final A+ closure", 31, 31, 0, 7, 14, 10, 0, 0)
```

Read as:

- `31` v22 theorem-spine rows tracked.
- `31` rows closed or audited as definitions/direct theorems/consequence projections.
- `0` residual gates remain.
- `7` definition-carrier rows.
- `14` direct Lean theorem rows.
- `10` consequence-projection rows.
- `0` explicit hypothesis-gate rows.
- `0` corpus-closure synthesis rows.

The current final A+ gate is true:

```lean
kernelAPlusFinalAPlusCurrentlyClosedBool = true
```

## Strength of the Result

The closed A+ result is not only a source crosswalk.  The formal theorem surface
includes:

- fixed-domain uniqueness: `KernelUniqueOnFixedDomain` and
  `PaperKernelUniquenessOnFixedDomainStatement`;
- non-derivability from below: `NoDerivationBelowKernel` and
  `PaperNothingDerivableBelowKernelStatement`;
- no faithful lower generator: `PaperKernelNonDerivabilityStatement`,
  `PaperNoFaithfulLowerGeneratorStatement`, and
  `PaperNoDeeperInvariantClosedStatement`;
- final synthesis: `PaperGlobalSynthesisUnderCorpusClosuresClosedStatement`.

These are included in the final A+ closure posture:
`31` theorem-spine rows tracked, `31` closed or audited, `0` residual gates,
and `0` hypothesis gates.

## Residual Gates

There are no remaining residual gate anchors.

The previous no-deeper-invariant residual item is now closed by:

```lean
PaperNoDeeperInvariantClosedStatement
```

The previous scope-preserving-invariance residual item is now closed by:

```lean
PaperScopePreservingInvarianceClosedStatement
```

The previous quotient-identity residual item is now closed by:

```lean
PaperQuotientIdentityClosedStatement
```

The previous structural-rigidity residual item is now closed by:

```lean
PaperStructuralRigidityOfAdmissibilityInvariantClosedStatement
```

The previous foundational-exhaustion residual item is now closed by:

```lean
PaperExhaustionOfFoundationalConditionsClosedStatement
```

The previous internal-mechanization-boundary residual item is now closed by:

```lean
PaperInternalMechanizationBoundaryClosedStatement
```

The previous global-synthesis residual item is now closed by:

```lean
PaperGlobalSynthesisUnderCorpusClosuresClosedStatement
```

## Canonical Audit Files

- `Checks/Axiom/MinimalConditionsAPlusAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusSourceCrosswalkAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusProgressLedgerAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusResidualGateLedgerAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusResidualGateCallabilityAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusResidualGateSupplyQueueAudit.lean`
- `Checks/Axiom/MinimalConditionsAPlusCurrentFocusAudit.lean`
- `Checks/Axiom/NonDegenerateConstructionAndKernelOfAdmissibilityAxiomCheck.lean`

## Current Focus

The final mathematical closure target is:

```lean
KernelGlobalSynthesisUnderCorpusClosures R
```

It is closed by:

```lean
kernelAPlusCurrentFocusTarget_closes_with_final_a_plus_certificate
```

The current-focus audit marks final closure as supplied.

## Interpretation

The v22 theorem spine is now source-crosswalked and audit-addressable in Lean.
The fixed-domain consequence layer, uniqueness/interior/conservation interface,
internal mechanization boundary, global synthesis, and audit metadata are
mechanically checked.  The v22 kernel paper theorem spine is now closed at the
A+ audit surface.
