# Release Notes

## AASC P vs NP SAT Endpoint Full-Stack Lean Audit Archive v1.0.7

This release packages the hardened Lean 4 audit archive for the AASC-first SAT
endpoint proof spine.

Included:

- P vs NP SAT endpoint Lean files under `MaleyLean/Papers/PvsNP`.
- The AASC foundation layer required by the SAT route, including Minimal
  Conditions, Nondegenerate Kernel, A+ certificate, Ametric-boundary,
  non-derivability, structural-rigidity, and global-synthesis anchors.
- Focused P vs NP SAT endpoint axiom checks and a combined full-stack AASC/SAT
  axiom check under `Checks/Axiom`.
- Encoded candidate model adequacy anchors, including
  `CnfEncodedCandidateModelAdequate`,
  `cnfSATInPolyTime_iff_exists_encoded_nonfailing_candidate`, and
  `cnfSATNotInPolyTime_iff_all_encoded_candidates_fail`, making the encoded
  model exact for ordinary deterministic polynomial-time CNF-SAT candidates.
- SAT negative occupation-exhaustion anchors, including
  `cnfSATNegativeOccupation_exhaustion` and
  `cnfSATNegativeOccupation_nonoptional`.
- SAT endpoint-status bivalence anchors, including
  `cnfSATGovernedEndpointUse_bivalent` and
  `cnfSATNegativeGovernedEndpointUse_has_separatorStatus`.
- SAT-native lower-bound normal-form and theorem-level discriminator anchors,
  including `cnfSATBareNegativeBranch_standardLowerBoundNormalForm` and
  `cnfSATBareNegativeBranch_theoremLevelDiscriminator`.
- A formal legitimate-invariant / forbidden endpoint-status-governance
  distinction via `CnfSATInvariantUseKind`.
- A candidate-image exclusion use fork via
  `CnfSATCandidateImageExclusionUseKind` and
  `CnfSATCandidateImageExclusionUseClassification`, with
  `cnfSATOfficialNegativeEndpointUse_endpointStatusGovernance` identifying
  official endpoint-resolving negative use as endpoint-status governance and
  `cnfSATEndpointResolvingNonGovernance_hiddenFifthCase_impossible` closing
  the endpoint-resolving-but-not-governance escape.
- Final official endpoint-evaluation hygiene through
  `CnfSATOfficialEndpointEvaluation`,
  `OfficialSATEndpointEvaluation`, and
  `cnfSATOfficialEndpointEvaluation_negativeBranch_endpointResolution`.
- Final separator-occupation unpacking through
  `cnfSATImageSeparatorEndpointUse_contains_candidateImageExclusion`, keeping
  support-level candidate-image exclusion distinct from endpoint occupation.
- Ordinary-practice closure through
  `cnfSATOrdinaryTheoremBearingNonOccupation_not_fifthEndpointRole`, recording
  that ordinary theorem-bearing non-occupation is not a fifth endpoint role
  once official endpoint use and SAT projection are fixed.
- Remaining same-mode objection exhaustion through
  `cnfSATRemainingSameModeObjections_exhausted`, with residual objections
  classified as SAT projection/carrier failure, endpoint-discriminator
  trichotomy failure, or A+ no-independent-discriminator consequence failure.
- Local reductio countercase routing through `CnfSATReductioCountercase`,
  `CnfSATLocalCountercase`, `CnfSATEndpointCounterforce`, and
  `cnfSATReductioCountercase_impossible_of_noIndependentDiscriminator`.
- A+ binding hardening through
  `CnfSATOrdinaryOfficialEndpointResolution`,
  `cnfSATOrdinaryOfficialEndpointResolution_is_endpointUse`,
  `CnfSATAPlusEndpointUseBinding`, and
  `cnfSATAPlusNotOptionalOverlay_on_ordinaryOfficialResolution`, recording
  that ordinary official endpoint resolution is endpoint use and that A+ is
  downstream of that role rather than an optional overlay.
- A+ consequence binders for the separator route:
  `cnfSATAPlusConsequences_bind_ordinaryOfficialNegativeResolution`,
  `cnfSATEndpointUse_trichotomy_binds_independentRole`,
  `cnfSATAPlusConsequences_bind_satSeparatorDiscriminator`, and
  `cnfSATAPlusConsequences_bind_localSeparatorCountercaseUse`.
- Official endpoint-resolution target-adequacy hardening through
  `CnfSATOfficialResolutionTargetAdequacy`,
  `cnfSATOfficialEndpointResolution_satisfies_targetAdequacy`, and
  `cnfSATOfficialResolutionTargetAdequacy_instantiates_kernelAPlus`,
  recording that official endpoint resolution in the fixed SAT
  route/model/domain context is target-adequate endpoint use bound by the
  kernel A+ certificate.
- Same-domain incompleteness/Godel defensive hardening through
  `CnfSATSameDomainIncompletenessRoute`,
  `CnfSATSameDomainIncompletenessEndpointObjection`,
  `cnfSATOfficialResolution_stable_against_sameDomainIncompleteness`, and
  `cnfSATNoSameDomainTrueButUnprovableSeparatorSplit`, routing same-domain
  incompleteness objections either to endpoint-inert support or to the already
  forbidden independent endpoint-gate role.
- Audit runner: `scripts/check-pvsnp-sat-operator-bridge-audit.ps1`.
- Manuscript-facing PDF/source and ledger artifacts when available from the
  workspace.
- Final manuscript snapshot refreshed from the June 11 front-facing official
  resolution adequacy bundle, including the A+ binding layer, target-adequacy
  clarification, same-domain incompleteness/Godel stability supplement, and
  companion source material under `papers/pvsnp/source_material`.
- Full-stack audit path exposed through
  `Checks/Axiom/PvsNPFullStackAASCAxiomCheck.lean`.

Verification command:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-pvsnp-sat-operator-bridge-audit.ps1
```

Audit framing:

- no live project-level `axiom`, `sorry`, `admit`, or `unsafe` declaration on
  the audited AASC foundation plus P vs NP SAT endpoint surface;
- `AASCSATEndpointClosure=100%`;
- `CnfSATInPolyTimeClosure=100%`;
- Cook-Levin/Karp is treated as external endpoint correspondence, not as proof
  machinery for the AASC separator exclusion;
- standard Lean/classical foundations may appear in dependency reports.

Pinned environment:

- Lean toolchain: `leanprover/lean4:v4.28.0`
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
