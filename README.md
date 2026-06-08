# AASC P vs NP SAT Endpoint Lean Audit

Standalone Lean 4 archive for the AASC-first SAT endpoint proof spine in:

`P != NP by Exclusion of the SAT Separator Endpoint`

This repository separates the P vs NP SAT endpoint audit surface from the
larger mixed AASC working checkout. It contains the P vs NP Lean files, the
AASC bivalence/minimal-conditions/kernel support spine needed by those files,
the focused axiom/audit checks, and the manuscript-facing PDF/source snapshot.

## Current Status

The strongest truthful claim for this archive is:

- `MaleyLean.Papers.PvsNP.SATOperatorAuditRunners` builds.
- The SAT endpoint proof queue and status ledger build in a standalone Lake
  project.
- The AASC SAT endpoint branch is closed at the formalized proof-spine layer:
  `CnfSATInPolyTime` is obtained from the AASC no-independent-discriminator
  route encoded in `SATOperatorProofQueue.lean`.
- The audit runner reports `AASCSATEndpointClosure=100%` and
  `CnfSATInPolyTimeClosure=100%`.
- The audited P vs NP SAT endpoint surface contains no live project-level
  `axiom`, `sorry`, `admit`, or `unsafe` declaration in
  `MaleyLean/Papers/PvsNP` or `Checks/Axiom`.
- Standard Lean/classical foundations may still appear in `#print axioms`
  output, especially `propext`, `Classical.choice`, and `Quot.sound`. Those are
  standard imported foundations, not project-specific SAT support axioms.

This archive should be read as an AASC endpoint-structure formalization whose
final internal carrier is the official CNF-SAT/SAT endpoint. Cook-Levin/Karp is
an external endpoint correspondence: it identifies the standard complexity
consequence once the CNF-SAT polynomial-time endpoint is obtained. It is not
used as proof machinery for the AASC branch exclusion.

## Verification

Use:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-pvsnp-sat-operator-bridge-audit.ps1
```

The audit runner:

- prints the Lean toolchain;
- prints the pinned mathlib manifest revision;
- builds `MaleyLean.Papers.PvsNP.SATOperatorAuditRunners`;
- evaluates the current formalization-status and progress summaries;
- scans the audited SAT endpoint surface for live `axiom`, `sorry`, `admit`,
  or `unsafe` declarations;
- builds the main SAT proof queue and bridge-callability modules;
- runs the seven focused P vs NP SAT endpoint axiom-check files.

Pinned environment:

- Lean toolchain: `leanprover/lean4:v4.28.0`
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

## Main Lean Anchors

The main proof-spine objects are in
`MaleyLean/Papers/PvsNP/SATOperatorProofQueue.lean`.

Key final anchors:

- `CnfSATClayEndpointImageContext`
- `CnfSATFixedEndpointDomain`
- `CnfSATContextBoundCNFModel`
- `CnfSATBareSeparator`
- `cnfSATBareSeparator_iff_bareNegativeBranch`
- `cnfSATBareSeparator_forces_imageSeparatorBranch`
- `CnfSATImageSeparatorEndpointUse`
- `cnfSATImageSeparatorBranch_endpointUse`
- `cnfPositiveEndpoint_of_noIndependentDiscriminator`
- `cnfSATInPolyTime_of_noIndependentDiscriminator`
- `cnfSATInPolyTime_of_context_noIndependentDiscriminator`
- `cnfSATBareSeparator_impossible_of_context_noIndependentDiscriminator`

The current status ledger is in
`MaleyLean/Papers/PvsNP/SATOperatorStatusLedger.lean`.

## Scope Boundary

The proof architecture is AASC-internal up to `CnfSATInPolyTime`. Classical
complexity theory enters only at the endpoint-correspondence layer: finite
CNF-SAT is the standard NP-complete carrier, and polynomial-time decidability
of that carrier gives the standard P versus NP consequence through the
Cook-Levin/Karp bridge.

This archive does not claim to rederive the Cook-Levin theorem, Karp
reductions, or the general textbook theory of NP-completeness inside Lean.
Those are treated as external endpoint-identification facts, not as the engine
of the branch exclusion.

## Repository Layout

- `MaleyLean/Papers/PvsNP/` - SAT endpoint proof spine and AASC bridge files.
- `MaleyLean/Papers/MinimalConditionsForAdmissibleConstruction/` - A+ support
  spine consumed by the SAT route.
- `MaleyLean/Papers/BivalenceNonDegenerateReasoning/` - bivalence support
  spine consumed by the AASC route.
- `MaleyLean/Papers/NonDegenerateConstructionAndKernelOfAdmissibility.lean` -
  kernel/admissibility support anchor.
- `Checks/Axiom/` - focused Lean axiom-print and audit entry points.
- `papers/pvsnp/` - manuscript-facing source/PDF snapshot, when present.
- `reports/ledgers/` - manuscript ledger artifacts, when present.

## Reading Order

Start with:

- `MaleyLean/Papers/PvsNP/SATOperatorFormalizationStatus.md`
- `scripts/check-pvsnp-sat-operator-bridge-audit.ps1`
- `MaleyLean/Papers/PvsNP/SATOperatorStatusLedger.lean`
- `MaleyLean/Papers/PvsNP/SATOperatorProofQueue.lean`
