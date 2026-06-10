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
- The AASC foundation layer used by the SAT route is present in the same
  standalone project and is part of the public audit path:
  `MinimalConditionsForAdmissibleConstruction`,
  `NonDegenerateConstructionAndKernelOfAdmissibility`, the A+ certificate
  layer, Ametric-boundary anchors, kernel non-derivability anchors, structural
  rigidity anchors, and global-synthesis anchors.
- The AASC SAT endpoint branch is closed at the formalized proof-spine layer:
  `CnfSATInPolyTime` is obtained from the AASC no-independent-discriminator
  route encoded in `SATOperatorProofQueue.lean`.
- The audit runner reports `AASCSATEndpointClosure=100%` and
  `CnfSATInPolyTimeClosure=100%`.
- The audited AASC foundation plus P vs NP SAT endpoint surface contains no live project-level
  `axiom`, `sorry`, `admit`, or `unsafe` declaration in
  the checked AASC/P vs NP source roots or `Checks/Axiom`.
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
- scans the audited AASC foundation plus SAT endpoint surface for live
  `axiom`, `sorry`, `admit`, or `unsafe` declarations;
- builds and audits the AASC foundation/kernel support modules used by the SAT
  route;
- builds the main SAT proof queue and bridge-callability modules;
- runs the focused P vs NP SAT endpoint axiom-check files and the combined
  full-stack AASC/SAT axiom check.

Pinned environment:

- Lean toolchain: `leanprover/lean4:v4.28.0`
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

## Main Lean Anchors

The main proof-spine objects are in
`MaleyLean/Papers/PvsNP/SATOperatorProofQueue.lean`.

Key AASC foundation anchors:

- `PaperTargetAdequacyForcesKernelRolesStatement`
- `PaperConstructionForcesKernelStatement`
- `PaperKernelNonDerivabilityStatement`
- `PaperNothingDerivableBelowKernelStatement`
- `PaperNecessityAndBivalenceOfAdmissibilityStatement`
- `PaperAMetricBoundaryAndNonParameterizationStatement`
- `PaperStructuralRigidityOfAdmissibilityInvariantClosedStatement`
- `PaperExhaustionOfFoundationalConditionsClosedStatement`
- `PaperGlobalSynthesisUnderCorpusClosuresClosedStatement`
- `KernelAPlusAuditCertificate.ofKernelPacketAndUniqueness`
- `KernelAPlusAuditCertificate.auditSurfaceComplete_holds`

Key final anchors:

- `CnfEncodedCandidateModelAdequate`
- `CnfSATCandidateModelCoverage`
- `CnfSATCandidateModelSoundness`
- `CnfSATCandidateFailureAdequacy`
- `CnfSATCandidateImageExactness`
- `cnfSATInPolyTime_iff_exists_encoded_nonfailing_candidate`
- `cnfSATNotInPolyTime_iff_all_encoded_candidates_fail`
- `CnfSATStandardLowerBoundNormalForm`
- `CnfSATCandidateEndpointImageExclusion`
- `CnfSATTheoremLevelEndpointStatusDiscriminator`
- `CnfSATInvariantUseKind`
- `CnfSATInvariantUseLegitimate`
- `CnfSATCandidateImageExclusionUseKind`
- `CnfSATCandidateImageExclusionUseClassification`
- `CnfSATEndpointStatusGovernanceByCandidateImageExclusion`
- `cnfSATImageSeparatorBranch_standardLowerBoundNormalForm`
- `cnfSATBareNegativeBranch_standardLowerBoundNormalForm`
- `cnfSATTheoremLevelEndpointStatusDiscriminator_of_candidateImageExclusion`
- `cnfSATImageSeparatorBranch_theoremLevelDiscriminator`
- `cnfSATBareNegativeBranch_theoremLevelDiscriminator`
- `cnfSATEndpointResolvingNonGovernance_hiddenFifthCase_impossible`
- `cnfSATOfficialNegativeEndpointUse_endpointStatusGovernance`
- `cnfSATEndpointResolvingNegativeTheorem_is_endpointStatusGovernance`
- `CnfSATOrdinaryTheoremBearingNonOccupation`
- `cnfSATOrdinaryTheoremBearingNonOccupation_not_fifthEndpointRole`
- `CnfSATRemainingSameModeObjectionTarget`
- `cnfSATRemainingSameModeObjections_exhausted`
- `CnfSATClayEndpointImageContext`
- `CnfSATFixedEndpointDomain`
- `CnfSATContextBoundCNFModel`
- `CnfSATBareSeparator`
- `cnfSATBareSeparator_iff_bareNegativeBranch`
- `cnfSATBareSeparator_forces_imageSeparatorBranch`
- `CnfSATImageSeparatorEndpointUse`
- `cnfSATImageSeparatorBranch_endpointUse`
- `cnfSATImageSeparatorEndpointUse_contains_candidateImageExclusion`
- `CnfSATOfficialNegativeEndpointUse`
- `CnfSATOfficialEndpointEvaluation`
- `OfficialSATEndpointEvaluation`
- `CnfSATOfficialEndpointResolution`
- `cnfSATOfficialEndpointEvaluation_negativeBranch_endpointResolution`
- `cnfSATOfficialNegativeEndpointUse_of_endpointResolution`
- `CnfSATNegativeOccupationExhaustion`
- `cnfSATNegativeOccupation_exhaustion`
- `cnfSATNegativeOccupation_nonoptional`
- `CnfSATEndpointStatus`
- `CnfSATGovernedEndpointUse`
- `cnfSATGovernedEndpointUse_bivalent`
- `cnfSATNegativeGovernedEndpointUse_has_separatorStatus`
- `cnfPositiveEndpoint_of_noIndependentDiscriminator`
- `cnfSATInPolyTime_of_noIndependentDiscriminator`
- `cnfSATInPolyTime_of_context_noIndependentDiscriminator`
- `cnfSATInPolyTime_of_officialEndpointEvaluation_noIndependentDiscriminator`
- `CnfSATReductioCountercase`
- `CnfSATLocalCountercase`
- `CnfSATEndpointCounterforce`
- `CnfSATLocalImageSeparatorOccupation`
- `cnfSATReductioCountercase_impossible_of_noIndependentDiscriminator`
- `cnfSATBareSeparator_impossible_of_context_noIndependentDiscriminator`

The current status ledger is in
`MaleyLean/Papers/PvsNP/SATOperatorStatusLedger.lean`.

The encoded model adequacy packet is ordinary complexity bookkeeping, not AASC
proof machinery. The model covers every deterministic polynomial-time CNF-SAT
candidate procedure, decodes only polynomial-time candidates from
`codeInPolyTime`, preserves SAT failure under equal decoded procedures, and is
exact for the endpoint: `CnfSATInPolyTime` iff some encoded polynomial-time
candidate does not fail SAT, while `Not CnfSATInPolyTime` iff every encoded
polynomial-time candidate fails SAT.

The candidate-image exclusion fork is now explicit in Lean. A
candidate-image exclusion used only as proof support is classified as
non-endpoint-resolving. A carrier-changing lower-bound claim is classified as
domain shift. The endpoint-resolving negative theorem case is classified as
endpoint-status governance by `cnfSATOfficialNegativeEndpointUse_endpointStatusGovernance`.
The alleged endpoint-resolving-but-not-governance alternative is the hidden
fifth case, and `cnfSATEndpointResolvingNonGovernance_hiddenFifthCase_impossible`
records that it has no inhabitant in the audited SAT endpoint surface.

The final endpoint-evaluation hygiene layer is also explicit.  The official
raw positive/separator evaluation is named by `CnfSATOfficialEndpointEvaluation`
and the manuscript-facing alias `OfficialSATEndpointEvaluation`.  If the raw
negative branch is reached inside that evaluation,
`cnfSATOfficialEndpointEvaluation_negativeBranch_endpointResolution` supplies
the official endpoint-resolution use; it does not assert the positive branch.
The one-way unpacking lemma
`cnfSATImageSeparatorEndpointUse_contains_candidateImageExclusion` records that
separator endpoint occupation contains candidate-image exclusion, while
candidate-image exclusion alone still does not create endpoint occupation.

The ordinary-practice closure layer is now explicit as well.  Ordinary
theorem-bearing non-occupation is not a fifth endpoint role:
`cnfSATOrdinaryTheoremBearingNonOccupation_not_fifthEndpointRole` routes
official theorem-bearing non-occupation into the endpoint-status governance
classification.  Remaining same-mode objections are exhausted by
`cnfSATRemainingSameModeObjections_exhausted`, and the local reductio route is
named through `CnfSATReductioCountercase`, `CnfSATLocalCountercase`,
`CnfSATEndpointCounterforce`, and
`cnfSATReductioCountercase_impossible_of_noIndependentDiscriminator`.

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
- `Checks/Axiom/` - focused Lean axiom-print and audit entry points, including
  `PvsNPFullStackAASCAxiomCheck.lean` for the foundation-to-SAT stack.
- `papers/pvsnp/` - manuscript-facing source/PDF snapshot, when present.
- `reports/ledgers/` - manuscript ledger artifacts, when present.

## Reading Order

Start with:

- `MaleyLean/Papers/PvsNP/SATOperatorFormalizationStatus.md`
- `scripts/check-pvsnp-sat-operator-bridge-audit.ps1`
- `MaleyLean/Papers/PvsNP/SATOperatorStatusLedger.lean`
- `MaleyLean/Papers/PvsNP/SATOperatorProofQueue.lean`
