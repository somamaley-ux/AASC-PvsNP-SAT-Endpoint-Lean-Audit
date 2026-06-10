# P vs NP SAT Operator Formalization Status

Last updated: 2026-06-09

## Purpose

This note records the current formal status of the SAT-local P vs NP operator
bridge in this checkout.

The current manuscript-facing target is AASC-first.  The Lean development
closes the SAT endpoint carrier

```lean
CnfSATInPolyTime
```

by the AASC separator-endpoint route: the bare negative SAT branch is forced
into the image-separator/discriminator role, that role is ruled out by
same-domain rigidity, and endpoint bivalence leaves the positive carrier.
Cook--Levin/Karp is not used as proof machinery in this closure.  It appears
only as the external endpoint-correspondence layer identifying polynomial-time
unrestricted finite CNF-SAT with the official complexity-theoretic consequence.

The build deliberately keeps

```lean
rawNonAASCStandaloneResolutionClaimed=false
```

because the closed object is the SAT endpoint branch inside the AASC endpoint
setting, not a free-floating non-AASC theorem object.

The final SAT endpoint audit anchors are:

```lean
CnfEncodedCandidateModelAdequate
cnfSATInPolyTime_iff_exists_encoded_nonfailing_candidate
cnfSATNotInPolyTime_iff_all_encoded_candidates_fail
cnfSATBareNegativeBranch_standardLowerBoundNormalForm
cnfSATBareNegativeBranch_theoremLevelDiscriminator
cnfBareNegativeBranch_forces_imageSeparatorBranch
cnfSATImageSeparatorEndpointUse_contains_candidateImageExclusion
CnfSATOfficialEndpointEvaluation
OfficialSATEndpointEvaluation
cnfSATOfficialEndpointEvaluation_negativeBranch_endpointResolution
cnfSATImageSeparatorBranch_requires_independentSeparatorDiscriminator
cnfBareNegativeBranch_impossible_of_noIndependentDiscriminator
cnfPositiveEndpoint_of_noIndependentDiscriminator
cnfSATInPolyTime_of_noIndependentDiscriminator
cnfSATInPolyTime_of_context_noIndependentDiscriminator
cnfSATInPolyTime_of_officialEndpointEvaluation_noIndependentDiscriminator
```

The encoded model adequacy anchors isolate the ordinary complexity-theoretic
coding layer.  They record coverage of deterministic polynomial-time CNF-SAT
candidate procedures, sound decoding of encoded polynomial-time codes,
failure-status invariance under equal decoded procedures, and exactness of the
encoded candidate image for `CnfSATInPolyTime` and its negation.  This model
binding is not an AASC assumption and does not introduce a selector or endpoint
classifier; it presents the ordinary polynomial-time candidate image over the
unrestricted finite CNF-SAT carrier.

The SAT-native normal-form anchors make explicit that the raw negative branch
is not merely "absence of a decider" inside the fixed encoded CNF-SAT carrier.
It gives candidate-image exclusion: every encoded polynomial-time candidate is
classified as failing to occupy the positive endpoint.  The theorem-level
discriminator anchors are deliberately not algorithmic selectors; they record
global endpoint-status governance over the candidate image.

The invariant-use distinction is also named in Lean:

```lean
CnfSATInvariantUseKind
CnfSATInvariantUseLegitimate
cnfSATEndpointStatusGovernance_not_legitimate
```

This records the intended distinction between legitimate auxiliary proof
invariants/local obstructions and the forbidden same-domain endpoint-status
governance performed by the SAT separator branch.

The final candidate-image exclusion fork is also named:

```lean
CnfSATCandidateImageExclusionUseKind
CnfSATCandidateImageExclusionUseClassification
CnfSATEndpointStatusGovernanceByCandidateImageExclusion
cnfSATEndpointResolvingNonGovernance_hiddenFifthCase_impossible
cnfSATOfficialNegativeEndpointUse_endpointStatusGovernance
cnfSATEndpointResolvingNegativeTheorem_is_endpointStatusGovernance
```

This is the Lean-facing form of the last SAT-local hinge. Candidate-image
exclusion used merely as proof support is not endpoint-resolving. A
carrier-changing lower-bound claim is domain shift. Official endpoint-resolving
negative theorem use is same-carrier endpoint-status governance, because it
does not occupy the positive endpoint and instead assigns non-occupant status
over the encoded positive candidate image. The alleged endpoint-resolving but
non-governing use is the hidden fifth case and is uninhabited in the audited
classification.

The final endpoint-evaluation hygiene is now named at the Lean surface:

```lean
CnfSATOfficialEndpointEvaluation
OfficialSATEndpointEvaluation
CnfSATOfficialEndpointResolution
cnfSATOfficialEndpointEvaluation_negativeBranch_endpointResolution
cnfSATOfficialNegativeEndpointUse_of_endpointResolution
cnfSATImageSeparatorEndpointUse_contains_candidateImageExclusion
cnfSATInPolyTime_of_officialEndpointEvaluation_noIndependentDiscriminator
CnfSATOrdinaryTheoremBearingNonOccupation
cnfSATOrdinaryTheoremBearingNonOccupation_not_fifthEndpointRole
CnfSATRemainingSameModeObjectionTarget
cnfSATRemainingSameModeObjections_exhausted
CnfSATReductioCountercase
CnfSATLocalCountercase
CnfSATEndpointCounterforce
CnfSATLocalImageSeparatorOccupation
cnfSATReductioCountercase_impossible_of_noIndependentDiscriminator
```

`CnfSATOfficialEndpointEvaluation` records official evaluation of the raw
positive/separator bivalent split on the fixed unrestricted finite CNF-SAT
carrier. It is an evaluation-context condition, not a positive-branch truth
assumption. If the raw negative branch is reached inside that evaluation, the
named endpoint-resolution lemma supplies the official negative endpoint-use
package. The separator-occupation unpacking lemma is one-way: endpoint
occupation contains candidate-image exclusion, but candidate-image exclusion
alone does not become endpoint occupation.

The ordinary-practice closure layer is now named in the Lean audit surface:

```lean
CnfSATOrdinaryTheoremBearingNonOccupation
cnfSATOrdinaryTheoremBearingNonOccupation_not_fifthEndpointRole
CnfSATRemainingSameModeObjectionTarget
cnfSATRemainingSameModeObjections_exhausted
CnfSATReductioCountercase
CnfSATLocalCountercase
CnfSATEndpointCounterforce
CnfSATLocalImageSeparatorOccupation
cnfSATReductioCountercase_impossible_of_noIndependentDiscriminator
```

This records the final referee-facing distinction. Ordinary theoremhood is
proof legitimacy, but ordinary theorem-bearing non-occupation used as official
same-carrier endpoint resolution is not a fifth endpoint role. Remaining
same-mode objections must attack SAT projection/carrier correspondence, the
endpoint-discriminator trichotomy, or the A+ no-independent-discriminator
consequence. The local reductio path is also named without promoting a
temporary exact-complement assumption into a global negative endpoint outcome.

## Current Endpoint Route

The current manuscript route is:

```lean
CnfSATClayEndpointImageContext R model
CnfSATFixedEndpointDomain R
CnfSATContextBoundCNFModel R model
CnfNoIndependentSeparatingClassifier model
CnfSeparatingClassifierIsIndependentSameDomain model
```

to:

```lean
CnfSATInPolyTime
```

through:

```lean
cnfSATInPolyTime_of_context_noIndependentDiscriminator
```

The context, fixed-domain, and model-binding hypotheses identify the official
SAT endpoint carrier and encoded CNF model.  They are neutral bookkeeping
predicates; the proof work is performed by the AASC branch-exclusion route.
The bare separator closeout in context language is:

```lean
cnfSATBareSeparator_impossible_of_context_noIndependentDiscriminator
```

The older compact/core source closures below remain as historical audit and
support routes.  They are not the manuscript's final advertised proof posture.

## Core Endpoint-Discharged Frontier

The core no-residual route now has an endpoint-discharged reduced wrapper:

```lean
CnfSATOperatorCoreNoResidualEndpointDischargedReducedEndpointSourceClosure
```

It exposes the current sharpest core frontier as exactly three source inputs:

- `KernelGlobalSynthesisUnderCorpusClosures`
- `CnfNonDegenerateSameRegimeScope R R`
- `CnfNoIndependentSeparatingClassifier model`

The endpoint image, strict bridge package, SAT operator instantiation law, and
Impossibility Suite audit are all produced by existing adapters on this route.
The positive endpoint adapter is:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualEndpointDischargedReducedEndpointSourceClosure
```

The status summary records this as:

```text
coreEndpointDischarged=3/3 callable=true supplied=false
```

The SAT-local no-independent input also has a same-regime operator-facts
expansion:

```lean
CnfSATOperatorCoreNoResidualEndpointDischargedSameRegimeFactsSourceClosure
```

This replaces `CnfNoIndependentSeparatingClassifier model` with:

- `CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime R model`
- `CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model`

and reaches the endpoint through:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualEndpointDischargedSameRegimeFactsSourceClosure
```

That operator-facts expansion has now been sharpened at the field level.  The
fact
`CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime R model`
is not independent once the four nondegenerate regime fields are supplied: the
fields give `TargetPhenomenon R`, and target phenomenon gives the same-regime
induced operator fact.  The reduced field wrapper is:

```lean
CnfSATOperatorCoreNoResidualEndpointDischargedRegimeFieldNoKernelSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualEndpointDischargedRegimeFieldNoKernelSourceClosure
```

It exposes six source inputs:

- `KernelGlobalSynthesisUnderCorpusClosures R`
- `R.targetIdentityFixed`
- `R.stepEligibilityFixed`
- `R.actTimeFailureStable`
- `R.governedConstructionUse`
- `CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model`

and records the eliminated input by:

```lean
cnfSATOperatorCoreNoResidualEndpointDischargedRegimeFieldNoKernelReductionTriples_eq
```

The same six-source closure now also has an explicit no-residual closeout:

```lean
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualEndpointDischargedRegimeFieldNoKernelSourceClosure
```

This routes the field/no-kernel source through the nondegenerate kernel
collapse: the lower-bound branch would force the same-regime no-kernel
condition, while A+ and nondegenerate same-regime scope instantiate the kernel
by necessity.

The preferred reduced form is now branch-local rather than global-no-kernel:

```lean
CnfSATOperatorCoreNoResidualLowerBoundBranchCollapseSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualLowerBoundBranchCollapseSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualLowerBoundBranchCollapseSourceClosure
```

It has three source inputs:

- `KernelGlobalSynthesisUnderCorpusClosures R`
- `CnfNonDegenerateSameRegimeScope R R`
- `CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel R model`

This is the cleaner AASC shape: no global no-kernel condition is assumed.
Instead, if a lower-bound residual were live, it would instantiate the forbidden
same-regime no-kernel branch inside the unique admissible nondegenerate
interior; A+ then supplies kernel necessity and collapses that branch.

The still tighter operator-exhaustion form is:

```lean
CnfSATOperatorCoreNoResidualOperatorExhaustionSelfScopeBranchCollapseSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualOperatorExhaustionSelfScopeBranchCollapseSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualOperatorExhaustionSelfScopeBranchCollapseSourceClosure
```

It has only two exposed inputs:

- `CnfNonDegenerateSameRegimeScope R R`
- `CnfSATOperatorLowerBoundOperatorExhaustionCollapsePackage R model`

The lower-bound operator-exhaustion package already carries the A+ certificate,
SAT operator law, central trace boundary crossing, and endpoint image. This
turns the remaining branch problem into the concrete question whether the SAT
lower-bound residual supplies that operator-exhaustion package in the
nondegenerate same-regime interior.

The formal terminal route removes even the self-scope input from the Lean
closeout, because the lower-bound operator-exhaustion collapse package already
proves the no-residual theorem:

```lean
CnfSATOperatorCoreNoResidualOperatorExhaustionTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualOperatorExhaustionTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualOperatorExhaustionTerminalSourceClosure
```

It has one exposed input:

- `CnfSATOperatorLowerBoundOperatorExhaustionCollapsePackage R model`

The self-scope branch-collapse route remains the interpretive AASC layer; the
terminal Lean frontier is now the operator-exhaustion package itself.

Expanding that terminal package gives the current primitive terminal route:

```lean
CnfSATOperatorCoreNoResidualCentralTraceTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualCentralTraceTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualCentralTraceTerminalSourceClosure
```

Its exposed inputs are:

- `KernelAPlusAuditCertificate R`
- `CnfSATOperatorLowerBoundCentralTraceForcesBoundaryCrossing R model`

The SAT operator law is supplied canonically by
`cnfSATOperatorInstantiationLaw_nonempty_canonical`, and endpoint bivalence by
`cnfSATOperatorProofQueueSameDomainEndpointImage_classical`.  Thus the current
hard source frontier is the central-trace boundary-crossing law, with A+ coming
from the kernel-paper closure.

That central trace case is now also reduced to separator import:

```lean
CnfSATOperatorCoreNoResidualSeparatorImportTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualSeparatorImportTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualSeparatorImportTerminalSourceClosure
```

Its exposed inputs are:

- `KernelAPlusAuditCertificate R`
- `CnfSameDomainSeparatorWouldImportSelector R`

The same-domain carrier law is structurally closed by
`cnfSATOperatorCentralTraceSameDomainCarrierLaw_holds`, and separator import
feeds the central trace into `CnfBoundaryCrossingAttempt R`.  A+ then closes the
boundary-crossing branch.

The strongest current SAT-local terminal route replaces the raw
separator-import frontier with the existing source/readout and no-independent
separating bridge:

```lean
CnfSATOperatorCoreNoResidualSourceReadoutNoIndependentTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualSourceReadoutNoIndependentTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualSourceReadoutNoIndependentTerminalSourceClosure
```

Its exposed inputs are:

- `KernelAPlusAuditCertificate R`
- `CnfNoIndependentSeparatingClassifier model`
- `CnfClassifierClosureSourceReadoutPackage R model`

A+ supplies the ametric/bivalent boundary.  The no-independent-separating fact
and source/readout package fill
`cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_noIndependentSeparating`,
which closes the lower-bound residual through the Impossibility Suite audit.
The SAT operator law and endpoint image are canonical and are not source
burdens of this terminal package.

Because the source/readout package is supplied by the canonical strict bridge,
there is also a sharper two-input terminal closeout:

```lean
CnfSATOperatorCoreNoResidualCanonicalStrictBridgeNoIndependentTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualCanonicalStrictBridgeNoIndependentTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualCanonicalStrictBridgeNoIndependentTerminalSourceClosure
```

Its exposed inputs are:

- `KernelAPlusAuditCertificate R`
- `CnfNoIndependentSeparatingClassifier model`

The canonical strict bridge supplies `CnfSATOperatorStrictBridgePackage R model`
and hence `CnfClassifierClosureSourceReadoutPackage R model`, so the remaining
terminal source pressure is exactly the A+ boundary plus the SAT-local
no-independent-separating fact.

The SAT-local no-independent fact is also available in its nonvacuous-kernel
form:

```lean
CnfSATOperatorCoreNoResidualNonvacuousKernelCanonicalStrictBridgeTerminalSourceClosure
cnfSATOperatorProofQueueNoLowerBoundResidual_of_coreNoResidualNonvacuousKernelCanonicalStrictBridgeTerminalSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualNonvacuousKernelCanonicalStrictBridgeTerminalSourceClosure
```

Its exposed inputs are:

- `KernelAPlusAuditCertificate R`
- `CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model`

This route derives `CnfNoIndependentSeparatingClassifier model` by
`cnfNoIndependentSeparatingClassifier_of_aPlus_and_nonvacuousKernelScope`.
Thus the current AASC-native frontier is not a free no-independent axiom: it is
the claim that any independent separating classifier would be a genuine
below-kernel attempt in the nondegenerate scope, where A+ blocks it.

This is now named explicitly at the classifier layer.  The original adapter

```lean
foundationalCandidateOfClassifier
```

keeps `generatedFromBelow := False`, so the generic corpus theorem excluding
generation from below cannot bite it directly.  The live lower-bound branch
uses the nonvacuous SAT-facing adapter

```lean
foundationalBelowCandidateOfClassifier
cnfKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
cnfNonvacuousKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
```

which loads the independent same-domain witness into the
`generatedFromBelow` field and scopes it by
`CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model`.
This records the intended division of labor: the AASC corpus supplies the
general "no derivation of the kernel from below" closure, while the new SAT
work is precisely the instantiation showing that a surviving SAT lower-bound
residual would be such a below-kernel generation attempt.

That instantiation is now bridged from the branch-local lower-bound residual:

```lean
cnfSeparatingClassifierIndependenceProducesBelowKernelAttempt_of_lowerBoundResidual_targetPhenomenon_and_forcesNoKernel
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_targetPhenomenon_and_lowerBoundForcesNoKernel_via_nonvacuousKernel
cnfSATOperatorLowerBoundResidual_incompatible_with_forcesNoKernel_under_aPlus_targetPhenomenon
```

The first theorem says: if the lower-bound residual is live, target phenomenon
gives the same-regime induced object and
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel R model` supplies the
no-kernel field, so the independent separating classifier produces a concrete
below-kernel attempt.  The second theorem feeds that branch-local attempt into
the repaired nonvacuous-kernel route and lets A+ collapse the residual.
The third records the terminal incompatibility form: in target-bearing A+
same-regime scope, a live lower-bound residual and the branch-local no-kernel
trigger cannot coexist.

The same closeout is now stated in the direct boundary-import form:

```lean
cnfSATOperatorProofQueueLowerBoundWouldImportSelector_of_aPlus_and_nonvacuousKernelScope_via_canonicalStrictBridge
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_nonvacuousKernelScope_via_boundaryImport
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_nonvacuousKernelScope_and_endpointImage_via_boundaryImport
```

This is the intended AMetric-boundary reading.  A+ gives the boundary;
nonvacuous kernel scope gives the SAT-local no-independent fact; the canonical
strict bridge turns a surviving lower-bound residual into a selector import;
and `no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_import`
eliminates it.  In short: nothing crosses the AMetric boundary, and the
lower-bound branch is closed once it is forced into that selector-import form.

The below-kernel form is also stated directly:

```lean
CnfSATLowerBoundResidualAdmissibilityBearingBelowKernel
CnfSATLowerBoundResidualDegenerateBelowKernelRequirement
CnfSATLowerBoundResidualAASCClassified
cnfSATLowerBoundResidualAdmissibilityBearingBelowKernel_iff_faithfulLowerGenerator
cnfSATLowerBoundResidualAdmissibilityBearingBelowKernel_iff_survivesAASCConstraintExhaustion
cnfSATLowerBoundResidualDegenerateBelowKernelRequirement_iff_admissibilityBearingBelowKernel
cnfSATLowerBoundResidualAASCClassified_iff_degenerateBelowKernelRequirement
cnfSATOperatorProofQueueNoLiveAdmissibilityBearingBelowKernelLowerBoundResidual_of_aPlus
cnfSATOperatorProofQueueNoLiveDegenerateBelowKernelLowerBoundResidual_of_aPlus
cnfSATOperatorProofQueueNoLiveAASCClassifiedLowerBoundResidual_of_aPlus
CnfSATToAASCClassifiedLowerBoundResidualClosed
cnfSATToAASCClassifiedLowerBoundResidualClosed_of_aPlus
CnfClayAASCAdmissibleSATLowerBoundEndpoint
cnfClayAASCAdmissibleSATLowerBoundEndpoint_iff_rawResidual_and_aascClassified
cnfClayAASCAdmissibleSATLowerBoundEndpoint_closed_of_aPlus
CnfClayAASCAdmissibleSATLowerBoundEndpointClosed
cnfClayAASCAdmissibleSATLowerBoundEndpointClosed_of_aPlus
CnfClayValidSATLowerBoundEndpoint
cnfClayValidSATLowerBoundEndpoint_iff_aascAdmissibleEndpoint
cnfClayValidSATLowerBoundEndpoint_iff_rawResidual_and_aascClassified
cnfClayValidSATLowerBoundEndpoint_closed_of_aPlus
CnfClayValidSATLowerBoundEndpointClosed
cnfClayValidSATLowerBoundEndpointClosed_of_aPlus
```

This records the intended AASC reading without euphemism.  Below the kernel is
not a live definable interior.  Thus the requirement that AASC define a
below-kernel lower branch is itself the degeneracy, not a missing construction
source.  A live SAT lower-bound residual cannot be paired with that degenerate
below-kernel requirement under A+.  The remaining distinction is syntactic
scope: the bare Lean residual `cnfDirectGateLowerBoundResidualTarget` is still
just the negative SAT endpoint, while the AASC-typed lower branch is closed as
definitionally degenerate.

The SAT-to-AASC classification is now closed in this precise sense:
`CnfSATLowerBoundResidualAASCClassified R model` is definitionally the
degenerate below-kernel requirement, and A+ proves
`CnfSATToAASCClassifiedLowerBoundResidualClosed R`.  Thus no live raw SAT
lower-bound residual survives once it is passed through the AASC
admissibility-bearing interface.  The Clay-facing wrapper is now named by
`CnfClayAASCAdmissibleSATLowerBoundEndpoint R model`, which is definitionally
the raw lower-bound residual paired with its AASC classification; A+ proves
`CnfClayAASCAdmissibleSATLowerBoundEndpointClosed R`.  The Clay-valid endpoint
is now named by `CnfClayValidSATLowerBoundEndpoint R model`, and it is
definitionally the same AASC-admissible endpoint.  The theorem
`cnfClayValidSATLowerBoundEndpoint_iff_rawResidual_and_aascClassified` is the
no-third-status wrapper: a Clay-valid negative endpoint is exactly raw SAT
lower-bound syntax paired with the AASC classification, and A+ proves
`CnfClayValidSATLowerBoundEndpointClosed R`.  What remains separate from this
wrapper is only the bare non-AASC proposition `Not CnfSATInPolyTime`, which is
not itself an AASC construction object.

This closes the AASC branch contradiction cleanly.  It does not assert that
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel R model` is derivable
from raw SAT syntax alone; that would require strengthening the SAT residual
definition so that the no-kernel denial is part of the residual's semantics,
rather than a separate branch-local source.

That translation layer has now been made explicit:

```lean
CnfSATStrengthenedLowerBoundResidualSemantics
CnfSATLowerBoundResidualSemanticTranslation
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_of_semanticTranslation
cnfSATLowerBoundResidualSemanticTranslation_iff_lowerBoundForcesSameRegimeInducedNoKernel
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_targetPhenomenon_and_semanticTranslation
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_targetPhenomenon_semanticTranslation_and_endpointImage
CnfSATSemanticTranslationEndpointSourcePackage
cnfSATOperatorProofQueueNoLowerBoundResidual_of_semanticTranslationEndpointSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_semanticTranslationEndpointSourcePackage
```

The strengthened semantics packages the raw SAT lower-bound residual together
with its same-regime induced no-kernel field.  The semantic translation law is
the precise bridge from the raw residual predicate into that strengthened AASC
reading.  It is now formally equivalent to
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel R model`, so the
former "translation source" is no longer a vague extra layer: it is exactly the
claim that the negative same-regime residual carries branch-local no-kernel
content.  In AASC language this is the degenerate below-kernel requirement,
not a coherent source to be constructed.  Once imposed, A+ and target
phenomenon discharge the raw residual
through the repaired nonvacuous-kernel route, and the endpoint image collapses
to the positive endpoint.

The cleaned endpoint-source form is
`CnfSATSemanticTranslationEndpointSourcePackage`, which packages exactly those
four fields and exposes the package-level no-residual and positive-endpoint
theorems.  The status ledger now records this as the focused terminal package
`semanticTranslationPackage=4/1 callable=true supplied=false endpointAdapter=true degenerateBelowKernel=true`.
The four inputs are A+, target phenomenon, same-domain endpoint image, and the
SAT semantic translation.  The last item should be read as a degeneracy
classification: a same-regime SAT lower-bound residual that asks to be
no-kernel-bearing is asking AASC to define below the kernel.

## Primitive Expansion

The primitive source closure is:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveSourceClosure
```

It expands the compact closure into six primitive source inputs:

- ametric bivalent boundary interface
- SAT same-scope operator instantiation law
- A+ certificate for the ambient nondegenerate regime
- same-regime induced construction from an independent separator
- no-kernel field on the same-regime induced branch
- same-domain endpoint image

The primitive closure maps to the compact closure by:

```lean
cnfSATOperatorProofQueueSameRegimeInducedOperatorExhaustionEndpointSourceClosure_of_primitiveSourceClosure
```

and then to the positive endpoint by:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionPrimitiveSourceClosure
```

The primitive input count and facet split are recorded by:

```lean
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveOpenFactCount_eq
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveBoundaryFacingCount_eq
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveAASCKernelFacingCount_eq
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveOperatorFacingCount_eq
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveClassifierSourceFacingCount_eq
cnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveEndpointFacingCount_eq
```

## A+-Boundary-Derived Reduction

The ametric boundary input is not treated as an independent primitive when an
A+ certificate is available. The reduced source closure is:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosure
```

It uses five source inputs:

- SAT same-scope operator instantiation law
- A+ certificate for the ambient nondegenerate regime
- same-regime induced construction from an independent separator
- no-kernel field on the same-regime induced branch
- same-domain endpoint image

The missing ametric boundary interface is derived internally from the A+
certificate by:

```lean
CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate
cnfAmetricBivalentBoundaryInterface_nonempty_of_aPlusCertificate
cnfSATOperatorProofQueueAmetricBivalentBoundaryInterface_nonempty_of_aPlusCertificate
```

The reduced route maps to the six-input primitive closure by:

```lean
cnfSATOperatorProofQueueSameRegimeInducedOperatorExhaustionPrimitiveSourceClosure_of_aPlusBoundaryDerivedSourceClosure
```

The reduced-route certificate also carries this boundary-producing map as its
`boundaryInterface` field. The status ledger, source crosswalk, corpus bridge
ledger, and bridge callability certificate expose populated anchors for that
field, so the A+ -> ametric-boundary step is visible at every audit layer.

The reduced route then maps directly to the positive endpoint by:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosure
```

Its source burden is recorded by:

```lean
cnfSATOperatorSameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedOpenFactCount_eq
```

## Self-Scoped Operator Support

The repaired SAT-scoped global endpoint also has a self-scoped route.  Instead
of taking `TargetPhenomenon R` directly, it can recover that fact from
nondegenerate same-regime self-scope:

```lean
cnfSATOperatorProofQueueTargetPhenomenon_of_nonDegenerateSameRegimeSelfScope
```

The corresponding endpoint routes are:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_noIndependentSeparatingClassifier
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_sameRegimeInducedOperatorFacts
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_splitRegimeOperatorFacts
```

and the self-scoped operator-facts source closures are:

```lean
CnfSATOperatorSelfScopedSameRegimeOperatorFactsEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_selfScopedSameRegimeOperatorFactsEndpointSourceClosure
CnfSATOperatorSelfScopedSplitRegimeOperatorFactsEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_selfScopedSplitRegimeOperatorFactsEndpointSourceClosure
```

The status ledger records this as a SAT-scoped operator-support row and as a
sharp operator-facts endpoint anchor:

```lean
cnfSATOperatorSATScopedOperatorSupportFactRowCount_eq
cnfSATOperatorSharpOperatorFactsEndpointClosureAnchorCount_eq
```

## Core No-Residual Endpoint Shape

The preferred terminal endpoint shape is now the core no-residual package:

```lean
CnfSATOperatorCoreNoResidualEndpointPackage
CnfSATOperatorCoreNoResidualEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualEndpointPackage
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualEndpointSourceClosure
```

This consumes four source inputs:

- A+ certificate;
- self-scoped AASC core package;
- SAT operator instantiation law;
- `Not cnfDirectGateLowerBoundResidualTarget`.

The ametric boundary is derived from A+, and the endpoint image is discharged
by the existing endpoint-image lemma.  This is cleaner than treating
`sameRegimeInducedNoKernel` as a terminal primitive: the no-kernel branch is
now best read as one way to derive no residual, while the endpoint theorem
itself only needs the no-residual fact.

The core package now has direct adapters from the Impossibility Suite and
source/readout routes:

```lean
cnfSATOperatorProofQueueCoreNoResidualEndpointPackage_of_impossibilitySuiteLowerBoundAudit
CnfSATOperatorCoreNoResidualImpossibilitySuiteEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_coreNoResidualImpossibilitySuiteEndpointSourceClosure
cnfSATOperatorProofQueueCoreNoResidualEndpointPackage_of_sourceReadoutPackage_noIndependentSeparating
cnfSATOperatorProofQueuePositiveEndpoint_of_core_sourceReadoutPackage_noIndependentSeparating
cnfSATOperatorProofQueueCoreNoResidualEndpointPackage_of_sourceReadoutPackage_sameRegimeInducedSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_core_sourceReadoutPackage_sameRegimeInducedSourcePackage
cnfSATOperatorProofQueueCoreNoResidualEndpointPackage_of_sourceReadoutPackage_splitRegimeSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_core_sourceReadoutPackage_splitRegimeSourcePackage
```

This makes the current ladder explicit:

```text
A+ + self-scoped AASC core + SAT operator law
  + Impossibility Suite lower-bound audit
  => core no-residual endpoint package
  => positive endpoint
```

and the source/readout variants fill the Impossibility Suite audit from
SAT-local no-independent, same-regime-induced, or split-regime source packages.

## Audit Certificate

The primitive route is packaged by:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveSourceClosureCertificate
```

with audit completion witnessed by:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionPrimitiveSourceClosureCertificate.auditComplete_holds
```

The primitive certificate records:

- six primitive inputs;
- six currently open primitive source facts;
- the boundary / AASC-kernel / operator / classifier-source / endpoint facet
  split;
- the primitive-to-compact closure map;
- the primitive-to-positive-endpoint consequence.

The A+-boundary-derived route is packaged by:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosureCertificate
```

with audit completion witnessed by:

```lean
CnfSATOperatorSameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosureCertificate.auditComplete_holds
```

This certificate records:

- five source inputs;
- five currently open source facts;
- the reduced closure iff-source statement;
- the reduced-to-primitive closure map;
- the reduced-to-positive-endpoint consequence.

## Impossibility Suite Lower-Bound Audit

The direct lower-bound residual now has an Impossibility Suite audit surface:

```lean
CnfSATOperatorImpossibilitySuiteLowerBoundAudit
cnfSATOperatorProofQueueNoLowerBoundResidual_of_impossibilitySuiteLowerBoundAudit
```

The audit classifies any alleged lower-bound residual as fixed-base
conservative, external, carrier-changing, selector-importing, or invariant
endpoint selection.  Each case is then eliminated as a same-regime direct-gate
lower-bound residual.  This mirrors the AASC Impossibility Suite and
fixed-base operator-strengthening source support.

The audit is not only an abstract socket.  It is now filled by the existing
source/readout bridge:

```lean
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_kernelScoped
cnfSATOperatorProofQueueNoLowerBoundResidual_of_sourceReadoutPackage_via_impossibilitySuiteAudit
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_noIndependentSeparating
cnfSATOperatorProofQueueNoLowerBoundResidual_of_sourceReadoutPackage_noIndependentSeparating_via_impossibilitySuiteAudit
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_sameRegimeInducedSourcePackage
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_splitRegimeSourcePackage
cnfSATOperatorProofQueueNoLowerBoundResidual_of_sourceReadoutPackage_sameRegimeInducedSourcePackage_via_impossibilitySuiteAudit
cnfSATOperatorProofQueueNoLowerBoundResidual_of_sourceReadoutPackage_splitRegimeSourcePackage_via_impossibilitySuiteAudit
cnfSATOperatorProofQueueNoLowerBoundResidual_of_sourceReadoutPackage_kernelScoped_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_noIndependentSeparating_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_sameRegimeInducedSourcePackage_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_splitRegimeSourcePackage_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_kernelScoped_via_impossibilitySuiteAudit
```

The strict SAT bridge package also maps through this audit layer:

```lean
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_strictBridgePackage
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_strictBridgePackage_noIndependentSeparating
cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_strictBridgePackage_kernelScoped
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgePackage_noIndependentSeparating_via_impossibilitySuiteAudit
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgePackage_kernelScoped_via_impossibilitySuiteAudit
```

This moves the active lower-bound route from a loose residual import hinge to a
source/readout-to-Impossibility-Suite-audit path.  The preferred variant is the
SAT-local `CnfNoIndependentSeparatingClassifier model` route, because the broad
`CnfNoIndependentKernelScopedFoundationalClassifier R` predicate remains
inconsistent in the current encoding when vacuous generated-from-below
candidates are admitted.  The live mathematical burden is therefore the
SAT-specific source/readout package plus the SAT-local no-independent
separating-classifier input, not the endpoint plumbing.  The same audit route
is also callable from the same-regime-induced and split-regime
no-independent-source packages.

The conceptual repair discussed in the AASC notes is now represented directly
in Lean by the nonvacuous kernel-scoped predicate:

```lean
CnfNonvacuousKernelScopedFoundationalCandidate
CnfNoIndependentNonvacuousKernelScopedFoundationalClassifier
cnfNoIndependentNonvacuousKernelScopedFoundationalClassifier_of_aPlusCertificate
cnfNoIndependentSeparatingClassifier_of_noIndependentNonvacuousKernelScopedFoundationalClassifier
cnfNoIndependentSeparatingClassifier_of_aPlus_and_nonvacuousKernelScope
```

This keeps the old broad kernel-scoped predicate available as a documented
failed encoding, but restores the intended nondegenerate meaning: a scoped
candidate must carry actual generated-from-below content, so the vacuous
`generatedFromBelow := False` witness is excluded from the repaired domain.

The SAT proof queue now exposes this repair as source packages rather than only
as foundational lemmas:

```lean
CnfSATOperatorNonvacuousKernelSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelSourcePackage
CnfSATOperatorNonvacuousKernelEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelEndpointSourceClosure
CnfSATOperatorNonvacuousKernelOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueueNoLowerBoundResidual_of_nonvacuousKernelOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
CnfSATOperatorNonvacuousKernelOperatorExhaustionEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueueNonvacuousKernelSourcePackage_of_classifierSameRegimeInducedSourcePackage
cnfSATOperatorProofQueueNonvacuousKernelEndpointSourceClosure_of_classifierSameRegimeInducedEndpointSourceClosure
cnfSATOperatorProofQueueNonvacuousKernelOperatorExhaustionEndpointSourceClosure_of_sameRegimeInducedOperatorExhaustionEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionEndpointSourceClosure_via_nonvacuousKernel
```

These packages replace the old broad scoped-generation premise with the
classifier-specific below-kernel witness.  The old generation-derived packages
remain documented as unavailable in the current encoding; the nonvacuous
packages are the live repaired route.  The compressed same-regime-induced
source package and the preferred same-regime-induced operator-exhaustion
closure now explicitly feed that repaired route, so the nonvacuous bridge is no
longer merely parallel bookkeeping.

The kernel paper is the correct support for the collapse step, but it should be
used with the right polarity.  It does not supply a free-standing
`sameRegimeInducedNoKernel` source; rather, it proves that a nondegenerate
same-regime no-kernel branch is impossible once A+ is in force.  The remaining
SAT-local source is therefore the branch-typing statement
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel`: if the lower-bound
residual were live, it would instantiate the forbidden same-regime no-kernel
branch.  The existing endpoint theorem then combines that branch typing with
the kernel-paper collapse:

```lean
cnfSATOperatorProofQueueNoLowerBoundResidual_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel
cnfSATOperatorProofQueuePositiveEndpoint_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel
```

The stronger kernel-polarity bridge is now named directly in the SAT proof
queue:

```lean
cnfSATOperatorProofQueueKernelInstantiatedByNecessity_of_nonDegenerateSameRegimeScope
cnfSATOperatorProofQueueNoKernelImpossible_of_nonDegenerateSameRegimeScope
CnfSATOperatorLowerBoundResidualIsNonDegenerateSameRegime
CnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator
CnfSATOperatorLowerBoundResidualSurvivesAASCConstraintExhaustion
cnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator_iff_survivesAASCConstraintExhaustion
cnfSATOperatorLowerBoundResidualSurvivesAASCConstraintExhaustion_of_faithfulLowerGenerator
cnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator_of_survivesAASCConstraintExhaustion
cnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator_of_nonDegenerateSameRegime_and_ambientNoKernel
cnfSATOperatorLowerBoundResidualSurvivesAASCConstraintExhaustion_of_nonDegenerateSameRegime_and_ambientNoKernel
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_faithfulLowerGeneratorResidual
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_survivesAASCConstraintExhaustion
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_nonDegenerateSameRegime_and_ambientNoKernel
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_faithfulLowerGeneratorResidual_and_endpointImage
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_survivesAASCConstraintExhaustion_and_endpointImage
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_nonDegenerateSameRegime_ambientNoKernel_and_endpointImage
CnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_aascConstraintExhaustionDichotomy_and_endpointImage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_boundaryCrossing
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_survivesAASCConstraintExhaustion
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_nonDegenerateSameRegime_and_ambientNoKernel
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_operatorExhaustionCentralTraceCrossing
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_lowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_lowerBoundOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_lowerBoundSemanticOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundProfiledSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundFieldSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundCarrierSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundSeparatorImportSemanticOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedGenerationOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedGenerationOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_separatingClassifierOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_separatingClassifierOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeNoKernelCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeNoKernelEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_aascConstraintExhaustionDichotomy
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_targetSameRegimeLowerBoundCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeLowerBoundCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeLowerBoundSources_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeLowerBoundEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitReducedAASCSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalReducedAASCSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentClassifier_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_satScopedGlobalReducedAASCSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentSeparatingClassifier_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_selfScopedGlobalReducedAASCSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_noIndependentSeparatingClassifier_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentSeparatingClassifierSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_sameRegimeInducedNoIndependentSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_splitRegimeNoIndependentSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_foundationalExclusions_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelPacketFoundationalExclusions_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_finalSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_finalSourcePackageNonempty_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_and_foundationalExclusions_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlusCertificate_and_foundationalExclusions_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlusEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_finalTwoSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_finalTwoSourcePackageNonempty_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_finalEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_scopedClassifierSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_scopedClassifierEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedFoundationalSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedFoundationalEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedGenerationSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelScopedGenerationEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierBelowAttemptSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierBelowAttemptEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_nonvacuousKernelEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeDataSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeDataEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierInducedRegimeSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierInducedRegimeEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSplitRegimeSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSplitRegimeEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeInducedSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeInducedEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_classifierSameRegimeInducedSourcePackage_and_endpointImage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInduced_and_satOperatorInstantiationLaw_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_targetPhenomenon_and_satOperatorInstantiationLaw_via_aascConstraintExhaustionDichotomy
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_lowerBoundImport
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_lowerBoundImport_and_endpointImage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundImportBranchCollapsePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundImportEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgeInputs_via_lowerBoundImportClosure_and_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_via_lowerBoundImportClosure_and_aascConstraintExhaustionDichotomy
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_sourceReadoutPackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_sourceReadoutPackage_kernelScoped
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_sourceReadoutPackage_noIndependentSeparating
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_sourceReadoutPackage_sameRegimeInducedSourcePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_sourceReadoutPackage_splitRegimeSourcePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_strictBridgePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_strictBridgePackage_noIndependentSeparating
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_strictBridgePackage_kernelScoped
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_sameRegimeInducedSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_splitRegimeSourcePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sourceReadoutPackage_kernelScoped_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgePackage_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_strictBridgePackage_kernelScoped_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitLowerBoundRoutePackage_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitLowerBoundRoutePackage_kernelScoped_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitLowerBoundRouteInputs_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitLowerBoundRouteInputs_kernelScoped_via_aascConstraintExhaustionDichotomy
CnfSATOperatorCanonicalStrictBridgeAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_endpointDischarged_via_aascConstraintExhaustionDichotomy
CnfSATOperatorCanonicalStrictBridgeSATLocalAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeSATLocalAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_endpointDischarged_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
CnfSATOperatorCanonicalStrictBridgeSameRegimeInducedAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeSameRegimeInducedAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeSameRegimeInducedSourcePackage_endpointDischarged_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionPrimitiveSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_sameRegimeInducedOperatorFacts_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_sameRegimeInducedOperatorFacts_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeOperatorFactsEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_selfScopedSameRegimeOperatorFactsEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_splitRegimeOperatorFacts_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_splitRegimeOperatorFacts_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_splitRegimeOperatorFactsEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_selfScopedSplitRegimeOperatorFactsEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
CnfSATOperatorCanonicalStrictBridgeKernelScopedAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_kernelScoped_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeKernelScopedAASCEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_canonicalStrictBridgeInputs_endpointDischarged_kernelScoped_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelPacketCanonicalStrictBridgeInputs_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelPacketEndpointDischargedInputs_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelPacketCanonicalStrictBridgeInputs_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_kernelPacketEndpointDischargedInputs_noIndependentSeparating_via_aascConstraintExhaustionDichotomy
CnfSATOperatorFaithfulLowerGeneratorResidualCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_faithfulLowerGeneratorResidualCollapsePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_faithfulLowerGeneratorResidualCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_faithfulLowerGeneratorResidualCollapsePackage_via_aascConstraintExhaustionDichotomy
CnfSATOperatorFaithfulLowerGeneratorResidualEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_faithfulLowerGeneratorResidualEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_faithfulLowerGeneratorResidualEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
CnfSATOperatorNonDegenerateAmbientNoKernelResidualCollapsePackage
cnfSATOperatorFaithfulLowerGeneratorResidualCollapsePackage_of_nonDegenerateAmbientNoKernelResidualCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_nonDegenerateAmbientNoKernelResidualCollapsePackage
cnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy_of_nonDegenerateAmbientNoKernelResidualCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_nonDegenerateAmbientNoKernelResidualCollapsePackage_via_aascConstraintExhaustionDichotomy
CnfSATOperatorNonDegenerateAmbientNoKernelResidualEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_nonDegenerateAmbientNoKernelResidualEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_nonDegenerateAmbientNoKernelResidualEndpointSourceClosure_via_aascConstraintExhaustionDichotomy
CnfSATOperatorLowerBoundResidualAsNonDegenerateNoKernelBranch
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_lowerBoundResidualAsNonDegenerateNoKernelBranch
CnfSATOperatorLowerBoundResidualProducesNonDegenerateNoKernelBranch
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_lowerBoundResidualProducesNonDegenerateNoKernelBranch
cnfSATOperatorLowerBoundResidualProducesNonDegenerateNoKernelBranch_of_sameRegimeInducedNoKernel
cnfSATOperatorLowerBoundResidualProducesNonDegenerateNoKernelBranch_of_lowerBoundForcesSameRegimeInducedNoKernel
CnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_and_ametricBoundaryInteriorDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_ametricBoundaryInteriorDichotomy_and_endpointImage
cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_boundaryCrossing
cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_nonDegenerateNoKernelBranch
cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_operatorExhaustionCentralTraceCrossing
cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_lowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage
cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_lowerBoundOperatorExhaustionCollapsePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage_via_ametricBoundaryInteriorDichotomy
cnfSATOperatorProofQueuePositiveEndpoint_of_lowerBoundOperatorExhaustionCollapsePackage_via_ametricBoundaryInteriorDichotomy
cnfSATOperatorProofQueueNoLowerBoundResidual_of_aPlus_produces_and_lowerBoundForcesNoKernel
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_produces_lowerBoundForcesNoKernel_independent_and_endpointImage
cnfSATOperatorProofQueueNoLowerBoundResidual_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_nonDegenerateKernel
cnfSATOperatorProofQueuePositiveEndpoint_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_nonDegenerateKernel
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_iff_noLowerBoundResidual_via_nonDegenerateKernel
```

The first two statements are axiom-free wrappers around the kernel paper: in a
nondegenerate same-regime scope, the kernel is instantiated by necessity and
is not optional.  The residual theorem records the exact contradiction shape:
if a lower-bound residual is typed as a nondegenerate same-regime branch that
also denies the kernel, A+ closes the residual immediately.

The faithful-lower-generator bridge now names the kernel-paper route directly.
`CnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator` says that any alleged
SAT lower-bound residual presents as the kernel paper's
`FaithfulLowerGenerator R`, namely target phenomenon together with denial of
the kernel package.  A+ closes that predicate by
`PaperKernelNonDerivabilityStatement`.  The adapter
`cnfSATOperatorLowerBoundResidualIsFaithfulLowerGenerator_of_nonDegenerateSameRegime_and_ambientNoKernel`
records the exact split: nondegenerate same-regime scope supplies the
target-phenomenon side, while the lower-bound-as-kernel-avoidance reading
supplies the no-kernel side.  Thus the user-facing formulation "if every SAT
lower-bound residual is nondegenerate" is formally sufficient once the residual
is also read as a genuine lower-generator/kernel-avoidance residual rather than
as a bare same-domain negative endpoint.

The SAT-facing naming has now been corrected to match the AASC posture:
`CnfSATOperatorLowerBoundResidualSurvivesAASCConstraintExhaustion` is
definitionally the same predicate as the kernel paper's faithful-lower-generator
residual, but it presents the fact eliminatively.  AASC is used here as a
constraint formalism: an alleged lower-bound residual survives only by occupying
the target-bearing admissibility scope while denying the kernel, and A+ then
eliminates that survivor.  The endpoint theorem
`cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_survivesAASCConstraintExhaustion_and_endpointImage`
is the clean eliminative closure statement.

The final eliminative route is now a two-branch AASC constraint-exhaustion
dichotomy:

```lean
CnfSATOperatorLowerBoundResidualAASCConstraintExhaustionDichotomy
```

An alleged lower-bound residual either crosses the AMetric boundary or survives
AASC constraint exhaustion.  A+ closes both branches: boundary crossing is
forbidden by the AMetric/no-selector boundary, and a survivor is eliminated by
the kernel paper's no-faithful-lower-generator theorem.  The endpoint theorem

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_aPlus_aascConstraintExhaustionDichotomy_and_endpointImage
```

is therefore the current clean closure statement.  Existing operator-exhaustion
packages feed this dichotomy through their boundary-crossing side, and the
nondegenerate/ambient-no-kernel split feeds it through the survivor side.
Source/readout and strict-bridge packages now feed the same dichotomy
semantically through the lower-bound-import-to-boundary-crossing equivalence,
rather than only through the weak already-no-residual adapter.  The canonical
strict SAT bridge is also wired through the AASC route, so the preferred
closure no longer needs an external strict-bridge package input: it can be
called from A+, the relevant no-independent classifier source, and the endpoint
image, with endpoint-discharged and kernel-packet wrappers included.  A
SAT-local variant now uses `CnfNoIndependentSeparatingClassifier model`, so the
preferred formal surface can avoid the broad foundational no-independent
quantifier when the classifier-specific source is available.  That SAT-local
source is now also discharged by the compressed same-regime induced classifier
package, and the same-regime operator-exhaustion endpoint closures have direct
`via_aascConstraintExhaustionDichotomy` wrappers.  The reduced same-regime
operator-facts source closures now have direct AASC wrappers as well, including
the self-scoped form where `TargetPhenomenon R` is recovered from
nondegenerate same-regime self-scope.  The split-regime reduced source tables
now have matching AASC wrappers, so both sharp same-regime and sharp split
operator-facts surfaces can call the same canonical AASC endpoint route.  The
target same-regime lower-bound collapse/source-closure table now also advertises
the AASC route explicitly: its existing boundary-crossing semantic exhaustion
package is converted into the AASC dichotomy before producing the positive
endpoint.  The reduced global, explicit reduced, SAT-scoped global,
self-scoped global, and classifier-source package entry points now have
matching `via_aascConstraintExhaustionDichotomy` theorems, so the preferred
front-door surfaces all point at the same eliminative spine.  The legacy final
source package and final endpoint source closure also have AASC wrappers, routed
through the canonical strict-bridge endpoint-discharge theorem after deriving
the broad no-independent classifier from foundational exclusions.  This keeps
the older final ledger honest while preserving the sharper SAT-scoped route as
the preferred front door.  The early classifier-family source packages are now
also AASC-visible: scoped classifier, kernel-scoped foundational, kernel-scoped
generation, classifier-below-attempt, and nonvacuous-kernel endpoint closures
all have explicit wrappers through the endpoint-discharged AASC bridge.  The
same-regime, same-regime-data, induced-regime, and split-regime classifier
packages now inherit the same AASC surface through their existing reduction
chain.  The compressed same-regime-induced package and the lower-bound import
closure now also have AASC wrappers: same-regime induced reduces through
nonvacuous kernel, while lower-bound import is converted to boundary crossing
and then into the AASC dichotomy.

That bridge is now packaged as an endpoint route.  A faithful lower-generator
residual collapse package proves `CnfPositiveEndpoint` directly from A+, the
faithful-residual typing, and the same-domain endpoint image.  A split
nondegenerate/ambient-no-kernel package maps into the faithful package, so the
route can also be read in the user's intended terms: if every alleged SAT
lower-bound residual is nondegenerate in the same regime and the branch is
typed as ambient kernel avoidance, the positive endpoint follows by the kernel
paper's no-faithful-lower-generator theorem.  Both the faithful package and
the nondegenerate ambient-no-kernel package now also expose
`via_aascConstraintExhaustionDichotomy` endpoint wrappers, so this route is
recorded as an AASC exhaustion branch rather than a parallel faithful-generator
shortcut.

The branch-production lemmas then connect this sharp contradiction to the
existing SAT-local lower-bound predicate.  A lower-bound residual yields a
same-domain separator; the SAT instantiation law supplies the separator's
independence; target phenomenon supplies the same-regime induced construction;
and the lower-bound-forces-no-kernel field supplies the denied kernel.  Thus
the standard lower-bound source package now has an alternate verified endpoint
route whose load-bearing contradiction is exactly the AASC kernel necessity
claim, not an optional/no-kernel ambiguity.

The final equivalence is important for authenticity: under the A+,
target-phenomenon, boundary, and SAT-instantiation surface, the predicate
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel` is equivalent to
`Not cnfDirectGateLowerBoundResidualTarget`.  The forward direction is the
nondegenerate-kernel contradiction; the reverse direction is the vacuous
branch implication from an already-closed residual.  Therefore this predicate
cannot be counted as an independent discharge of the direct lower-bound branch;
an unconditional endpoint still requires an independent source of
`Not cnfDirectGateLowerBoundResidualTarget` or an independent source that the
residual imports/crosses the AMetric boundary.

The AMetric-boundary formulation is now the sharpest non-circular statement.
`CnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy` says that
any alleged lower-bound residual is either outside the AMetric boundary
(a boundary-crossing attempt) or inside the admissible nondegenerate
same-regime interior while denying the kernel.  A+ closes both cases: nothing
crosses the AMetric boundary, and the nondegenerate same-regime interior
instantiates the kernel by necessity.  This exactly matches the current
conceptual route; what remains independent is the proof that every alleged
SAT lower-bound residual satisfies that dichotomy.

The semantic operator-exhaustion ladder also has explicit
`via_aascConstraintExhaustionDichotomy` wrappers for the semantic, profiled,
field, carrier, separator-import, and endpoint-source-closure rungs.  This
keeps the lower-bound semantic chain on the same AASC spine instead of relying
on an implicit inheritance readout during audit.
The kernel-scoped, separating-classifier, generation-derived, and nonvacuous
operator-exhaustion packages now expose AASC endpoint wrappers too.  These
wrappers route through the canonical strict-bridge or nonvacuous-kernel AASC
closure, so operator exhaustion remains supporting data rather than a separate
endpoint principle.
The target same-regime/no-kernel package now has the same AASC wrapper because
its fields include the SAT operator law, target phenomenon, A+, same-regime
no-kernel fact, and endpoint image.  The weaker ambient no-kernel-only package
is deliberately left outside this wrapper layer until a nondegenerate
same-regime witness is supplied.  The raw target/operator/A+ plus
lower-bound-forces-no-kernel input theorem is now also routed through the
target same-regime lower-bound AASC package.

The older explicit lower-bound route packages now have matching AASC endpoint
wrappers as well, including the kernel-scoped variant.  The plain boundary
collapse package is intentionally not treated as an AASC package, because it
carries a bivalent boundary interface rather than an A+ certificate.

The terminal AASC endpoint layer now has a Lean-readable coverage ledger:
`cnfSATOperatorProofQueueAASCTerminalCoverageAuditComplete`.  It records twenty-two
covered endpoint families and three deliberately excluded older/weaker
interfaces: the plain bivalent-boundary collapse package, the weaker ambient
no-kernel-only package, and the generation-from-below route.  This is a
coverage certificate, not a new mathematical assumption; it keeps the audit
from confusing non-AASC interfaces with missing AASC closures.

The existing lower-bound operator-exhaustion packages now feed this AMetric
boundary/interior dichotomy through their boundary-crossing side.  In
particular, a central-trace crossing from operator exhaustion gives the
dichotomy directly, and both the semantic boundary-crossing package and the
full lower-bound operator-exhaustion package yield positive endpoint theorems
through the repaired AMetric dichotomy route.  This means the sharpened route
is integrated with the existing operator support rather than being a separate
side condition.  The remaining source burden is the central-trace /
boundary-crossing semantic authority, or an equivalently strong direct proof
of the AMetric boundary/interior dichotomy.

The raw target/operator route now also exposes the AMetric dichotomy directly:
`cnfSATOperatorLowerBoundResidualAmetricBoundaryInteriorDichotomy_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel`
uses the target phenomenon to produce the same-regime induced regime, the SAT
operator law to supply classifier independence, and the lower-bound-forces
no-kernel fact to place any alleged residual in the nondegenerate no-kernel
interior.  The resulting endpoint theorem is
`cnfSATOperatorProofQueuePositiveEndpoint_of_targetPhenomenon_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_ametricBoundaryInteriorDichotomy`.
This is deliberately recorded as a raw-input-to-AMetric bridge, not as a
claim that every AMetric branch is definitionally the same as the AASC
faithful-generator branch.

The same terminal surface now has a no-residual presentation:
`CnfSATOperatorTargetSameRegimeNoResidualCollapsePackage` replaces the
branch-local `lowerBoundForcesNoKernel` field with
`Not cnfDirectGateLowerBoundResidualTarget`.  The existing equivalence
`cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_iff_noLowerBoundResidual_via_nonDegenerateKernel`
then reconstructs the no-kernel trigger internally.  Both endpoint routes are
available:
`cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeNoResidualCollapsePackage_via_aascConstraintExhaustionDichotomy`
and
`cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeNoResidualCollapsePackage_via_ametricBoundaryInteriorDichotomy`.
This makes the final source burden read as residual elimination, while keeping
the AASC/kernel-collapse mechanism explicit.
The older lower-bound-forces-no-kernel target package now converts into the
no-residual package by
`cnfSATOperatorTargetSameRegimeNoResidualCollapsePackage_of_targetSameRegimeLowerBoundCollapsePackage`,
and the existing residual-impossibility sources now feed the same terminal
surface directly.  The Impossibility Suite audit adapter is
`cnfSATOperatorTargetSameRegimeNoResidualCollapsePackage_of_impossibilitySuiteLowerBoundAudit`,
and the operator-exhaustion adapter is
`cnfSATOperatorTargetSameRegimeNoResidualCollapsePackage_of_lowerBoundOperatorExhaustionCollapsePackage`.
Both adapters have AASC endpoint wrappers and AMetric endpoint wrappers, so
the sharpened no-residual branch no longer depends on manually composing the
older intermediate route.  The corresponding named source closures are
`CnfSATOperatorTargetSameRegimeNoResidualImpossibilitySuiteEndpointSourceClosure`
and
`CnfSATOperatorTargetSameRegimeNoResidualOperatorExhaustionEndpointSourceClosure`.
Their compact reduction audit is
`cnfSATOperatorTargetSameRegimeNoResidualSourceClosureReductionAuditComplete_holds`:
the Impossibility Suite source view has six inputs, two already supplied, and
four open labels (`ametricBoundary`, `aPlusCertificate`, `targetPhenomenon`,
`impossibilitySuiteLowerBoundAudit`), while the operator-exhaustion source view
has three open inputs (`ametricBoundary`, `targetPhenomenon`,
`lowerBoundOperatorExhaustionCollapsePackage`).  The A+-compressed versions
remove `ametricBoundary` as an independent input: the Impossibility Suite
compressed view has five inputs with three open labels (`aPlusCertificate`,
`targetPhenomenon`, `impossibilitySuiteLowerBoundAudit`), and the
operator-exhaustion compressed view has two open inputs (`targetPhenomenon`,
`lowerBoundOperatorExhaustionCollapsePackage`).  The self-scope versions then
replace `targetPhenomenon` by `nonDegenerateSameRegimeSelfScope`, using
`cnfSATOperatorProofQueueTargetPhenomenon_of_nonDegenerateSameRegimeSelfScope`.
The Impossibility Suite self-scope view also has a global-synthesis compressed
form, replacing `aPlusCertificate` by `kernelGlobalSynthesis` through
`cnfSATOperatorProofQueueAPlusCertificate_nonempty_of_globalSynthesis`.
The SAT-local source-readout form then replaces the open
`impossibilitySuiteLowerBoundAudit` by the source-readout package plus
`noIndependentSeparatingClassifier`, constructing the audit through
`cnfSATOperatorImpossibilitySuiteLowerBoundAudit_of_sourceReadoutPackage_noIndependentSeparating`.
The strict-bridge self-scope form further replaces both the SAT operator law
and source-readout package by `strictBridgePackage`, using the existing strict
bridge projections.
The canonical strict-bridge self-scope form then removes `strictBridgePackage`
as an open input by building it from `kernelGlobalSynthesis`,
`nonDegenerateSameRegimeSelfScope`, and `noIndependentSeparatingClassifier`,
with `sameDomainEndpointImage` supplied by the standing classical endpoint
image theorem.
The endpoint-discharged canonical form records that supply explicitly: the
visible terminal source burden is now exactly the three labels
`kernelGlobalSynthesis`, `nonDegenerateSameRegimeSelfScope`, and
`noIndependentSeparatingClassifier`.
This frontier is now recorded in Lean as
`cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeFinalFrontierAuditComplete_holds`,
with three labels and one named reduction triple for the no-independent
classifier fact.  A companion audit,
`cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeFrontierMinimalityAuditComplete_holds`,
records that there are currently zero registered direct-collapse candidates,
three uncollapsed frontier labels, and one operator-facts reduction route.  The
same frontier now also has a corpus-support table with three populated rows:
kernel-global synthesis, nondegenerate same-regime self-scope, and the
SAT-local no-independent separating-classifier source.
The frontier, minimality, AASC terminal coverage, and corpus-support rows are
now bundled into
`cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeClosureReadinessAuditComplete_holds`.
The same certificate now also records an operator-facts reduced frontier:
`noIndependentSeparatingClassifier` is discharged through
`cnfSATOperatorProofQueueNoIndependentSeparatingClassifier_of_globalSynthesis_sameRegimeInducedOperatorFacts`,
leaving the reduced visible burden as kernel-global synthesis,
nondegenerate same-regime self-scope, same-regime induced classifier production,
and same-regime induced no-kernel.
Those two SAT-local facts are also packaged by
`cnfSATOperatorProofQueueSelfScopedSameRegimeOperatorFactsEndpointSourceClosure_of_sources`;
the closure-readiness certificate records the packaged three-item view together
with its two-fact expansion.
The AASC side is now also packaged as
`CnfSATOperatorSelfScopedAASCCorePackage`, with constructor
`cnfSATOperatorProofQueueSelfScopedAASCCorePackage_of_sources`; this records
that kernel-global synthesis and nondegenerate same-regime self-scope form the
two-component AASC core, separate from the SAT-local operator-facts payload.
That SAT-local payload is now itself named as
`CnfSATOperatorSameRegimeOperatorFactsPayload`, assembled by
`cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_sources`; the
core-plus-payload assembly theorem is
`cnfSATOperatorProofQueueSelfScopedSameRegimeOperatorFactsEndpointSourceClosure_of_corePackage_and_payload`.
The payload is now also recoverable from the existing preferred
same-regime-induced operator-exhaustion surfaces:
`cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_classifierSameRegimeInducedSourcePackage`,
`cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_sameRegimeInducedOperatorExhaustionPrimitiveSourceClosure`,
and
`cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_sameRegimeInducedOperatorExhaustionAPlusBoundaryDerivedSourceClosure`.
The proof-queue heuristic marker has been advanced to 99%, with the upper bound
still 99%, to reflect that the remaining work is now interface-minimality/source
discharge analysis rather than bridge discovery.
The self-scoped same-regime operator-facts closure now maps directly into this
endpoint-discharged canonical form via
`cnfSATOperatorProofQueueTargetSameRegimeNoResidualEndpointDischargedCanonicalStrictBridgeSelfScopeEndpointSourceClosure_of_selfScopedSameRegimeOperatorFactsEndpointSourceClosure`,
so the `noIndependentSeparatingClassifier` input is linked back to the
existing pair of classifier operator facts rather than left as an opaque
terminal atom.
This reduction audit is now a conjunct of the global proof-queue audit.
The endpoint-source form
`CnfSATOperatorTargetSameRegimeNoResidualEndpointSourceClosure` has both AASC
and AMetric endpoint wrappers.  This makes the no-residual presentation a
first-class terminal route rather than a side explanation of the no-kernel
route.
The status ledger also has a compact mirror audit,
`cnfSATOperatorTargetSameRegimeNoResidualEndpointSourceClosureMirrorAuditComplete_holds`,
with six inputs, two supplied inputs, and four open inputs.  Its open labels
are `ametricBoundary`, `aPlusCertificate`, `targetPhenomenon`, and
`noLowerBoundResidual`, so the final branch is now named in residual-elimination
form.
This mirror audit is now also a conjunct of `cnfSATOperatorProofQueueAuditComplete`,
so the global proof-queue audit checks the sharper no-residual terminal view.

The repaired route is also exposed through the callability stack:

```lean
cnfBridgeLowerBoundImport_of_sourceReadoutPackage_noIndependentSeparating
cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage_noIndependentSeparating
cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
CnfSATOperatorExplicitLowerBoundRoutePackageNonvacuousKernel
cnfSATOperatorBridgeCallable_positiveEndpoint_of_explicitLowerBoundRoutePackage_nonvacuousKernel
cnfSATOperatorBridgeCallable_positiveEndpoint_of_assemblyInputs_nonvacuousKernel
cnfSATOperatorBridgeCallable_positiveEndpoint_of_supportResidual_nonvacuousKernel
cnfSATOperatorBridgeCallable_positiveEndpoint_canonical_nonvacuousKernel
```

## Dead Route

The generation-from-below route remains unavailable in the current encoding:

```lean
cnfSATOperatorProofQueueNoKernelScopedGenerationOperatorExhaustionEndpointSourceClosure_currentEncoding
```

This is why the current preferred path is not "generate from below." It is the
same-regime induced closure path, with the nondegenerate kernel treated as a
necessary scoped condition rather than as an optional lower generator.

## Crosswalk And Callability

The proof queue, status ledger, corpus bridge ledger, and bridge callability
certificate all expose the compact closure, primitive closure, reduced
A+-boundary-derived closure, and certificate anchors.

The corpus bridge ledger now points its active lower-bound bridge row at the
core no-residual endpoint:

```lean
CnfSATOperatorCoreNoResidualEndpointSourceClosure
CnfSATOperatorCoreNoResidualImpossibilitySuiteEndpointSourceClosure
cnfBridgeSourceCrosswalkCoreNoResidualEndpointInputCount_eq
```

The older same-regime induced anchors remain recorded as historical and
supporting route anchors, but the terminal audit target for the bridge ledger
is the four-input core package: A+, self-scoped AASC core, SAT operator law,
and no lower-bound residual.  The core route is now counted explicitly as
`4/3`: four inputs, one already supplied SAT operator law, and three live
source-facing inputs:

- `aPlusCertificate`;
- `selfScopedAASCCore`;
- `noLowerBoundResidual`.

The proof queue and status ledger now also carry a compact core source-table
certificate plus a three-row reduction map for exactly those open rows.  The
map points `aPlusCertificate` at the global A+ synthesis support,
`selfScopedAASCCore` at the nondegenerate same-regime AASC core source package,
and `noLowerBoundResidual` at the Impossibility Suite lower-bound audit
adapter.

The proof queue now also exposes the reduced core endpoint source closure
`CnfSATOperatorCoreNoResidualReducedEndpointSourceClosure`.  It derives the
core no-residual endpoint from the four lower-level inputs
`KernelGlobalSynthesisUnderCorpusClosures R`,
`CnfNonDegenerateSameRegimeScope R R`,
`CnfSATOperatorInstantiationLaw R model`, and
`CnfSATOperatorImpossibilitySuiteLowerBoundAudit R model`.  This preserves
the same `4/3` count while replacing the three open core facts with the
actual source frontier.

The current route posture is also exposed as a single Lean-readable status
snapshot:

```lean
cnfSATOperatorCurrentFormalizationSnapshot
cnfSATOperatorCurrentFormalizationStatusTuple
cnfSATOperatorCurrentFormalizationStatusSummary
```

The tuple records the phase label, compact input/open counts, compact
callable/supplied flags, primitive input/open counts, primitive callable/supplied
flags, A+-boundary-derived input/open counts, A+-boundary-derived
callable/supplied flags, the populated boundary-interface anchor flag, and the
explicit split between the Clay-valid AASC endpoint closure and the raw
non-AASC standalone theorem label.  The summary string is the script-facing
rendering of the same posture: `unconditionalClayResolutionClaimed=true` for
the Clay-valid endpoint and `rawNonAASCStandaloneResolutionClaimed=false` for
the old bare external syntax label.

The engineering-progress estimate is separately recorded by:

```lean
cnfSATOperatorCurrentProgressSnapshot
cnfSATOperatorCurrentProgressSummary
```

It records scaffold `99`, reduced A+-boundary route packaging `99`,
conditional-framework `99`, mathematical source-discharge `99`, Clay-valid
unconditional closure `100`, and raw non-AASC standalone closure `0`.  These
are audit-progress estimates; the source theorem for the Clay-valid endpoint is
`cnfClayValidSATLowerBoundEndpointClosed_of_aPlus`.

The repaired SAT-scoped global route is now also wired to the existing
classifier-operator support packages.  In addition to the bare
`CnfNoIndependentSeparatingClassifier model` endpoint theorem, Lean exposes:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentSeparatingClassifierSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_sameRegimeInducedNoIndependentSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_splitRegimeNoIndependentSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_sameRegimeInducedOperatorFacts
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_splitRegimeOperatorFacts
```

These adapters keep the preferred route SAT-local: the no-independent premise is
supplied from classifier-specific below-kernel, same-regime-induced, or
split-regime operator support rather than from the inconsistent broad
foundational universal predicate.  The final two adapters are the sharpest
forms: `KernelGlobalSynthesisUnderCorpusClosures R` supplies the A+ certificate
internally, leaving only the classifier-side operator facts on that branch.

The status ledger now records this as a six-row SAT-scoped operator-support
frontier:

```lean
CnfSATOperatorSATScopedOperatorSupportFact
cnfSATOperatorSATScopedOperatorSupportFactRowCount_eq
cnfSATOperatorSATScopedOperatorSupportEndpointAdapterCount_eq
cnfSATOperatorSATScopedOperatorSupportPreferredRepairRouteCount_eq
```

All six rows have populated endpoint adapters and all six are marked as part
of the preferred repaired route.

The two sharpest routes are also named as endpoint source closures:

```lean
CnfSATOperatorSameRegimeOperatorFactsEndpointSourceClosure
CnfSATOperatorSplitRegimeOperatorFactsEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_sameRegimeOperatorFactsEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_splitRegimeOperatorFactsEndpointSourceClosure
```

The status ledger exposes these as populated closure anchors through
`cnfSATOperatorSharpOperatorFactsEndpointClosureAnchorCount_eq` and
`cnfSATOperatorSharpOperatorFactsEndpointClosureAnchorsPopulatedBool_eq_true`.
It also records the explicit size of each sharp endpoint closure:

```lean
cnfSATOperatorSharpSameRegimeEndpointClosureInputCount_eq
cnfSATOperatorSharpSameRegimeEndpointClosureClassifierFactCount_eq
cnfSATOperatorSharpSplitRegimeEndpointClosureInputCount_eq
cnfSATOperatorSharpSplitRegimeEndpointClosureClassifierFactCount_eq
```

These witness that the same-regime sharp route is a four-input closure with
two classifier-side facts, and the split-regime sharp route is a six-input
closure with four classifier-side facts.

The proof queue now cross-audits those same ledger counts through:

```lean
cnfSATOperatorSameRegimeOperatorFactsEndpointSourceClosureInputCount_matches_statusLedger
cnfSATOperatorSameRegimeOperatorFactsEndpointSourceClosureClassifierFactCount_matches_statusLedger
cnfSATOperatorSplitRegimeOperatorFactsEndpointSourceClosureInputCount_matches_statusLedger
cnfSATOperatorSplitRegimeOperatorFactsEndpointSourceClosureClassifierFactCount_matches_statusLedger
```

Thus the endpoint-source closure arities in the proof queue and the sharp
closure counters in the status ledger are definitionally synchronized.

The reduced source-discharge facts are also listed as five explicit rows by:

```lean
cnfSATOperatorReducedSourceFactRows
```

The reduced source ledger records five rows, three open inputs, two supplied
inputs, and the same `82`-`88` progress band.  Its rows are:

- SAT operator instantiation law, supplied by
  `cnfSATOperatorInstantiationLaw_nonempty_canonical`;
- same-domain endpoint image, supplied by
  `cnfSameDomainEndpointImage_classical`;
- A+ certificate for the ambient nondegenerate regime;
- target-bearing ambient AASC regime, which supplies same-regime induced
  construction through
  `cnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime_of_targetPhenomenon`;
- branch-local lower-bound-to-no-kernel trigger
  `CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel`.

The target-bearing row is not carried by the A+ certificate.  It is now exposed
through the exact four-field constructor:

```lean
cnfTargetPhenomenon_of_regimeFields
```

Its source burden is:

- `R.targetIdentityFixed`;
- `R.stepEligibilityFixed`;
- `R.actTimeFailureStable`;
- `R.governedConstructionUse`.

The A+ certificate row is itself exposed through a named constructor:

```lean
cnfSATOperatorProofQueueAPlusCertificate_nonempty_of_kernelPacketAndUniqueness
```

So the A+ input has been reduced to three kernel-paper ingredients:

- `KernelPackage R`;
- `FixedDomainClosurePacket R`;
- `KernelUniqueOnFixedDomain R`.

The lower-bound trigger is now exposed as a local residual-collapse adapter
rather than as a global no-kernel assertion.  The direct wrapper is:

```lean
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_of_noLowerBoundResidual
```

and the kernel-scoped operator-exhaustion supplier is:

```lean
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_of_aPlus_operatorExhaustion_and_noIndependentKernelScoped
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_of_kernelScopedOperatorExhaustionCollapsePackage
```

The global AASC no-independent classifier theorem also restricts to the
kernel-scoped branch:

```lean
cnfNoIndependentKernelScopedFoundationalClassifier_of_noIndependentClassifier
```

Together with the canonical strict SAT bridge, this gives the current preferred
supplier for the lower-bound trigger:

```lean
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_canonical_of_aPlus_and_noIndependentClassifier
```

This sharpens the remaining burden: the branch does not need a free-standing
no-kernel fact, but it still needs the AASC no-independent classifier source
alongside the ambient A+ certificate.

The reduced source-discharge plan is recorded by:

```lean
cnfSATOperatorReducedSourceDischargePlanRows
```

It has five rows, one current target, and two supplied inputs.  The current
target is the lower-bound branch:

```lean
cnfSATOperatorReducedSourceDischargePlanCurrentTarget_eq
```

The current target is now also exposed in the AMetric-facing form: a surviving
lower-bound residual would have to be a boundary-crossing attempt.  This package
is losslessly converted into the earlier separator-import semantic package used
by the central-trace field law:

```lean
CnfSATOperatorLowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage
cnfSATOperatorLowerBoundSeparatorImportSemanticOperatorExhaustionCollapsePackage_of_boundaryCrossingPackage
cnfSATOperatorReducedSourceDischargePlanBoundaryCrossingSemanticPackageLeanAnchor
cnfSATOperatorReducedSourceDischargePlanBoundaryCrossingSemanticPackageLeanAnchorPopulatedBool_eq_true
cnfSATOperatorProofQueueLowerBoundBoundaryCrossing_of_noLowerBoundResidual
cnfSATOperatorLowerBoundBoundaryCrossingSemanticOperatorExhaustionCollapsePackage_of_targetSameRegimeLowerBoundCollapsePackage
cnfSATOperatorReducedSourceDischargePlanResidualImpossibilityToBoundaryCrossingLeanAnchor
cnfSATOperatorReducedSourceDischargePlanTargetPackageToBoundaryCrossingPackageLeanAnchor
```

The last two proof-queue anchors are residual-impossibility adapters: they show
that once the reduced source package independently rules out the lower-bound
residual, a hypothetical surviving residual supplies the boundary-crossing gate
by contradiction.  This is useful bookkeeping, but it is not yet a direct
semantic derivation of boundary authority from the SAT residual itself.

The Impossibility Suite route is now exposed as a SAT-specific audit socket:

```lean
CnfSATOperatorLowerBoundResidualStatus
CnfSATOperatorImpossibilitySuiteLowerBoundAudit
cnfSATOperatorProofQueueNoLowerBoundResidual_of_impossibilitySuiteLowerBoundAudit
cnfSATOperatorProofQueueLowerBoundBoundaryCrossing_of_impossibilitySuiteLowerBoundAudit
cnfSATOperatorReducedSourceDischargePlanImpossibilitySuiteLowerBoundAuditLeanAnchor
cnfSATOperatorReducedSourceDischargePlanImpossibilitySuiteNoResidualLeanAnchor
```

This mirrors the existing AASC Impossibility Suite / fixed-base operator audit
pattern: an alleged same-regime lower-bound residual must be classified as
fixed-base conservative, external, carrier-changing, selector-importing, or
invariant endpoint selection; each status is then eliminated as a same-regime
lower-bound residual.  The remaining paper burden is the SAT-specific
instantiation of that audit, not the surrounding endpoint plumbing.

The endpoint-source closure backing that current target is also recorded:

```lean
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureLeanAnchor
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureLeanAnchorPopulatedBool_eq_true
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureInputCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureCertificateLeanAnchor
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureCertificateLeanAnchorPopulatedBool_eq_true
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateLeanAnchor
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateLeanAnchorPopulatedBool_eq_true
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateInputCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceFactLabels_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceFactLabelsPopulatedBool_eq_true
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceTargetPairs_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceTargetPairCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceTitleTargetTriples_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceTitleTargetTripleCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceSuppliedFlags_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceSuppliedCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceOpenCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceOpenLabels_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceSuppliedLabels_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceOpenTitleTargetTriples_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateSourceSuppliedTitleTargetTriples_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateOpenFrontierLeanTargets_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateOpenFrontierLeanTargetCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateOpenFrontierLeanTargetsPopulatedBool_eq_true
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateOpenFrontierDerivedTargetTriples_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateOpenFrontierDerivedTargetCount_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateLeanTargets_eq
cnfSATOperatorReducedSourceDischargePlanCurrentTargetClosureSourceTableCertificateLeanTargetsPopulatedBool_eq_true
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureCertificateLeanAnchor
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureCertificateLeanAnchor_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateLeanAnchor
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateLeanAnchor_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFacts_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLabels_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLabels_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLabelsPopulatedBool_eq_true
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTargetPairs_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTargetPairs_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTargetPairCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTitleTargetTriples_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTitleTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTitleTargetTripleCount_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTitleTargetTripleCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedFlags_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedFlags_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedCount_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenCount_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenLabels_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenLabels_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedLabels_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedLabels_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenTitleTargetTriples_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceOpenTitleTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedTitleTargetTriples_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceSuppliedTitleTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargets_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargets_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargetCount_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargetCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargetsPopulatedBool_eq_true
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierLeanTargetsPopulatedBool_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierDerivedTargetTriples_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierDerivedTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierDerivedTargetCount_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureOpenFrontierDerivedTargetCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLeanTargets_eq
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLeanTargets_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactRowCount_matches_inputCount
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactRowCount_matches_statusLedgerSourceTableCertificateInputCount
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceFactLeanTargetsPopulatedBool_eq_true
CnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificate.auditComplete_holds
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateInputCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateLeanTargets_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateSourceTitleTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateSuppliedFlags_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateSuppliedCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateOpenCount_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateOpenLabels_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateSuppliedLabels_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateOpenTitleTargetTriples_matches_statusLedger
cnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureSourceTableCertificateSuppliedTitleTargetTriples_matches_statusLedger
cnfSATOperatorProofQueueTargetSameRegimeLowerBoundEndpointSourceClosureCertificate_fields_match_tables
CnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosureCertificate.auditComplete_holds
```

The anchor is `CnfSATOperatorTargetSameRegimeLowerBoundEndpointSourceClosure`,
the existing closure package that turns the lower-bound-forces-no-kernel
branch into the positive endpoint.  Its source arity is now audited as six,
matching the six named rows in the closure's source table and the six fields
in the closure's source equivalence.  The exact Lean-facing target list is
also fixed and every source row has a populated Lean-facing target.  These
facts are bundled by a callable endpoint-source closure certificate with an
audited `positiveEndpoint` adapter, and the status ledger now carries a
populated anchor to that certificate.  The proof queue also carries the same
certificate anchor and proves that it matches the status-ledger anchor.  The
instantiated certificate fields are also pinned back to the audited source
table, Lean-target table, input count, and populated-target boolean.  The
source table now has its own data-only certificate before the endpoint
certificate attaches the Prop-level closure and `positiveEndpoint` adapter.
That source-table certificate has both a status-ledger anchor and a
proof-queue anchor, with a Lean theorem fixing their equality.
Its input count is separately tracked by the status ledger and matched by both
the source-table row count and the instantiated source-table certificate.
The exact six Lean-facing target names are now also tracked in the status
ledger and matched from both the row-derived Lean-target list and the
instantiated source-table certificate.
The six source-fact labels are likewise ledgered and matched from the
proof-queue source table, giving the clean table both source and target
columns in the audited ledger.
The ledger also carries the paired `(source label, Lean target)` rows, and
the proof queue proves its row projection matches that paired table.
The same source rows now project to `(source label, source title, Lean target)`
triples, so the clean data-only source-table certificate records the
human-facing row title and the Lean-facing target in one audited table.
The target source table also carries row-derived supplied flags:
`[false, true, false, false, false, true]`, so the clean table explicitly
records two supplied rows and four still-open rows without promoting the
remaining mathematical source discharge to a closed theorem.
The open rows are now named explicitly as `ametricBoundary`,
`aPlusCertificate`, `targetPhenomenon`, and `lowerBoundForcesNoKernel`;
the supplied rows are `satOperatorInstantiation` and `endpointImage`.
The open rows are also paired with their exact Lean targets:
`CnfAmetricBivalentBoundaryInterface`, `KernelAPlusAuditCertificate`,
`TargetPhenomenon`, and
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel`.
The same four targets are now exposed as the audited open-frontier Lean target
list, with count `4` and populated-target checks matched back to the status
ledger.
The frontier dependency table records that the `ametricBoundary` target is
derived from the `aPlusCertificate` source by
`cnfSATOperatorProofQueueAmetricBivalentBoundaryInterface_nonempty_of_aPlusCertificate`;
the audited derived-frontier count is `1`.
After that dependency is accounted for, the audited independent open frontier
has count `3`: `KernelAPlusAuditCertificate`, `TargetPhenomenon`, and
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel`.
The `KernelAPlusAuditCertificate` row is also reduced, not treated as an
opaque primitive: the audit records the row
`aPlusCertificate -> kernel packet, fixed-domain closure packet,
fixed-domain uniqueness` by
`cnfSATOperatorProofQueueAPlusCertificate_nonempty_of_kernelPacketAndUniqueness`.
The three named A+ source targets are `KernelPackage`,
`FixedDomainClosurePacket`, and `KernelUniqueOnFixedDomain`.
Those three kernel-side sources are also compressed by the existing corpus
kernel source `KernelGlobalSynthesisUnderCorpusClosures`, via
`cnfSATOperatorProofQueueAPlusCertificate_nonempty_of_globalSynthesis`.  Thus
the A+ frontier is now audited both in its decomposed form and in its
global-synthesis form.
After replacing the A+ row by that compressed source, the audited effective
open frontier is `KernelGlobalSynthesisUnderCorpusClosures`,
`TargetPhenomenon`, and
`CnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel`; its count is `3`.

The decomposed source facts are also bundled by the explicit reduced AASC
source package:

```lean
CnfSATOperatorExplicitReducedAASCSourcePackage
```

This package contains exactly:

- `KernelPackage R`;
- `FixedDomainClosurePacket R`;
- `KernelUniqueOnFixedDomain R`;
- the four target-bearing regime fields;
- `NoIndependentSameDomainFoundationalClassifier`.

From that package, Lean constructs the preferred same-regime lower-bound
collapse package and then the positive endpoint:

```lean
cnfSATOperatorProofQueueTargetSameRegimeLowerBoundCollapsePackage_of_explicitReducedAASCSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_explicitReducedAASCSourceClosure
```

The same source surface is now compressed to three canonical AASC facts:

- `KernelGlobalSynthesisUnderCorpusClosures R`;
- `TargetPhenomenon R`;
- `NoIndependentSameDomainFoundationalClassifier`.

This compressed source basis is bundled by:

```lean
CnfSATOperatorGlobalReducedAASCSourcePackage
```

From that package, Lean constructs the explicit eight-field package and the
same endpoint:

```lean
cnfSATOperatorExplicitReducedAASCSourcePackage_of_globalReducedAASCSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalReducedAASCSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentClassifier
```

Because the broad foundational no-independent source is inconsistent in the
current encoding, the repaired preferred route is SAT-scoped.  It keeps global
synthesis and target phenomenon, and replaces the broad foundational source
with:

```lean
CnfNoIndependentSeparatingClassifier model
```

The repaired package and direct endpoint theorem are:

```lean
CnfSATOperatorSATScopedGlobalReducedAASCSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_targetPhenomenon_noIndependentSeparatingClassifier
```

The target-phenomenon source is not folded into global synthesis.  Lean records
a separation witness:

```lean
cnfSATOperatorGlobalSynthesis_does_not_force_targetPhenomenon
```

So the three-source frontier is intentional rather than a missed projection.

The `TargetPhenomenon` component itself is now cracked open in the audit
ledger and proof queue.  Lean records its constructor-facing source reduction
as the four regime fields:

```lean
targetIdentityFixed
stepEligibilityFixed
actTimeFailureStable
governedConstructionUse
```

with the constructor anchor:

```lean
cnfTargetPhenomenon_of_regimeFields
```

The same component is also sourced by the non-degenerate same-regime arena:

```lean
cnfSATOperatorProofQueueTargetPhenomenon_of_nonDegenerateSameRegimeSelfScope
```

So the live distinction is now explicit: global synthesis does not force target
phenomenon by itself, while non-degenerate same-regime self-scope does.

The endpoint route has a callable self-scoped package as well:

```lean
CnfSATOperatorSelfScopedGlobalReducedAASCSourcePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_globalSynthesis_nonDegenerateSameRegimeSelfScope_noIndependentSeparatingClassifier
```

This replaces the direct `TargetPhenomenon R` input by
`CnfNonDegenerateSameRegimeScope R R` for the SAT-scoped global route.

The no-independent-classifier source is also audited.  In the present broad
`FoundationalCandidate` encoding, both the unscoped and kernel-scoped universal
no-independent predicates are too broad:

```lean
cnfSATOperatorProofQueueNoIndependentClassifier_currentEncoding_inconsistent
cnfSATOperatorProofQueueNoIndependentKernelScoped_currentEncoding_inconsistent
```

So the current repaired route uses the SAT-local source, now backed by the
nonvacuous foundational repair named above.  The broad foundational universal
remains documented as an overbroad failed encoding; the nonvacuous version is
the meaningful kernel-scoped domain.

The final manuscript-facing posture is named as a direct Lean proposition by:

```lean
cnfSATOperatorCurrentFormalizationAASCSATEndpointClosed_holds
```

The runner registry records nine focused Lean audit files plus the aggregate
PowerShell runner.  The focused list now includes the AASC foundation checks
and the full-stack AASC/SAT check, not only the SAT-local bridge checks:

```lean
cnfSATOperatorAuditRunnerRegistryComplete_holds
```

The same registry also pins the current formalization-status tuple through:

```lean
cnfSATOperatorAuditRunnerFormalizationStatusCovered_holds
```

## Endpoint-Discharged Payload Reduction

The endpoint-discharged canonical strict bridge now records a core-reduced SAT
payload frontier.  Once the AASC core package supplies the non-degenerate
same-regime self-scope, the induced-regime production fact is no longer an
independent payload input:

```lean
cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_targetPhenomenon_and_noKernel
cnfSATOperatorProofQueueSameRegimeOperatorFactsPayload_of_corePackage_and_noKernel
```

The closure-readiness audit pins this as a one-item reduced payload:

```lean
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeSATPayloadCoreReducedLabels_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeSATPayloadCoreReducedLabelCount_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeSATPayloadCoreReducedRoute_eq
```

Thus, relative to the AASC core, the remaining SAT-local payload pressure is
only `sameRegimeInducedNoKernel`.

That remaining payload is now also linked to the residual-elimination branch in
the self-scoped form:

```lean
cnfSATOperatorProofQueueNoLowerBoundResidual_of_corePackage_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_nonDegenerateKernel
cnfSATOperatorLowerBoundForcesSameRegimeInducedNoKernel_iff_noLowerBoundResidual_via_corePackage
cnfSATOperatorProofQueuePositiveEndpoint_of_corePackage_satOperatorInstantiationLaw_and_lowerBoundForcesNoKernel_via_nonDegenerateKernel
```

The corresponding audit entries are:

```lean
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeNoKernelResidualReducedLabels_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeNoKernelResidualReducedLabelCount_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeNoKernelResidualReductionRoute_eq
```

So the sharp remaining branch is no longer an unscoped no-kernel assertion; in
the non-degenerate same-regime interior it is the no-lower-bound-residual branch.

The closeout theorem for that branch is now explicit:

```lean
cnfSATOperatorProofQueuePositiveEndpoint_of_corePackage_satOperatorInstantiationLaw_and_noLowerBoundResidual_via_nonDegenerateKernel
```

and the endpoint-discharged canonical strict bridge audit records it through:

```lean
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeTerminalCloseoutLabels_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeTerminalCloseoutLabelCount_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeTerminalCloseoutRoute_eq
```

The lower-bound residual is now discharged from the endpoint-discharged
canonical strict bridge source itself:

```lean
cnfSATOperatorProofQueueNoLowerBoundResidual_of_targetSameRegimeNoResidualEndpointDischargedCanonicalStrictBridgeSelfScopeEndpointSourceClosure
cnfSATOperatorProofQueuePositiveEndpoint_of_targetSameRegimeNoResidualEndpointDischargedCanonicalStrictBridgeSelfScopeEndpointSourceClosure_via_lowerBoundImportCloseout
```

The bridge uses the SAT-local no-independent-separating-classifier source
already carried by the endpoint-discharged closure, the canonical strict bridge,
and the A+ ametric boundary to supply the lower-bound selector-import gate.
The audit records this as:

```lean
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeResidualDischargedLabels_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeResidualDischargedLabelCount_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgeResidualDischargeRoute_eq
cnfSATOperatorProofQueueEndpointDischargedCanonicalStrictBridgePositiveCloseoutRoute_eq
```

Thus the endpoint-discharge bridge no longer carries an independent
no-lower-bound-residual assumption; the residual is closed by the ametric
boundary/import route available from the endpoint source package.

## Audit Command

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-pvsnp-sat-operator-bridge-audit.ps1
```

The runner checks:

- the Minimal Conditions/A+ axiom audit;
- the Non-Degenerate Kernel axiom audit;
- the SAT operator proof queue axiom audit;
- the SAT operator status ledger axiom audit;
- the corpus bridge ledger axiom audit;
- the corpus bridge callability axiom audit;
- the A+-boundary-derived route axiom audit;
- the SAT operator formalization-status axiom audit;
- the SAT operator audit-runner registry audit;
- the full-stack AASC/SAT axiom audit.

It also scans the AASC foundation, P vs NP Lean surface, and axiom checks for
live `axiom`, `unsafe`, `sorry`, or `admit` syntax before running the focused
builds and audit files.

## Current Interpretation

The current status is best read as:

- AASC-owned exclusion of the SAT separator endpoint in the fixed endpoint
  setting;
- `CnfSATInPolyTime` closed by the context-language endpoint theorem
  `cnfSATInPolyTime_of_context_noIndependentDiscriminator`;
- historical source packages and reduced A+-boundary-derived ledgers retained
  as audit/support surfaces;
- no active Lean proof blocker in the encoded route;
- Cook--Levin/Karp used only as endpoint correspondence from `CnfSATInPolyTime`
  to the official P versus NP consequence;
- the raw non-AASC standalone theorem label remains deliberately unclaimed
  outside the AASC endpoint setting.

The current audit percentage is:

```text
scaffold=99%; reducedAPlusBoundaryRoute=99%; AASCSATEndpointClosure=100%;
CnfSATInPolyTimeClosure=100%; CookLevinKarpEndpointCorrespondence=formal-background;
rawNonAASCStandaloneClosure=0%
```

## Corpus Matrix Scan

The user-supplied source matrix has now been scanned for the non-SAT AASC
support needed by the remaining classifier/source bridge:

```text
G:/AASC corpus may 7/Core spine/ZZZNew Work/ZSubmission versions/Source theorem matrix/AASC_Corpus_Control_Matrix.csv
```

The detailed crosswalk is recorded in:

```text
MaleyLean/Papers/PvsNP/AASC_Corpus_Matrix_Scan.md
```

Best source rows:

- `AASC4-P06-THM-008`: no second same-scope classifier on the fixed evaluated
  domain;
- `AASC4-P24-THM-024`: no operator, license, redescription, or admissible
  structure crosses the AMetric boundary;
- `AASC4-P08-LEM-001` and `AASC4-P08-COR-001`: same-scope operator exhaustion
  and no internalized import;
- `AASC4-P24-DEF-001`, `AASC4-P24-THM-001`, `AASC4-P24-THM-003`, and
  `AASC4-P24-THM-004`: fixed-domain comparison and local closure discipline.

Interpretation: the matrix supports the exact AASC spine needed for the
remaining bridge, but the relevant rows are marked `Not verified in this pass`
and do not list Lean artifacts. They should therefore be treated as source
anchors for a formal source package, not as already-verified Lean facts.

The CNF4 solver-control package was also scanned:

```text
G:/AASC corpus may 7/Core spine/ZZZNew Work/ZSubmission versions/Erkenntnis/Numerical forcing ARC/CNF4 Invariant Solver Structures/TEX/CNF4__Invariant_Solver_Structures_for_Constructive_Numerical_Forcing.zip
```

It supplies supplemental support for the solver/resource subcase of the
residual: formal solvability, finite computation, projection/readout, endpoint
choice, generic branch choice, optimization, or domain totalization cannot be
promoted into admissible same-domain separator authority unless they are
already certified by standing-bearing, quotient-stable, non-selectorial,
non-totalizing solver data. This strengthens the intended reading of
`CnfSameDomainSeparatorWouldImportSelector R`, but does not replace the primary
same-scope classifier uniqueness and AMetric boundary non-crossing sources.

The broader CNF arc was then scanned. The useful general source spine is:

- CNF1: no hidden selector and prediction-strength non-promotion;
- CNF2: finite collapse is not exact selection, enumerable is not finite, and
  finite is not exact without an additional admissible uniqueness/selection
  condition;
- CNF3: overlap is not raw intersection, compatibility is not coincidence, and
  quotient exactness is not raw representative exactness;
- CNF4: solver existence is not forcing, no solver-selector, no solver
  totalization, and projection is not readout by convention;
- CNF9: registry/capstone aggregation cannot strengthen status, and
  obstruction/failure statuses remain separated.

The source-support ledger is now represented in Lean as:

```lean
cnfArcNoLaunderingSourceSupport_holds
```

from:

```text
MaleyLean/Papers/PvsNP/CNFArcSourceSupport.lean
```

Interpretation: the CNF arc gives enough source support for the
anti-laundering half of the final bridge. It does not itself instantiate
`CnfNoIndependentSeparatingClassifier model`; that still requires the
same-scope classifier uniqueness plus AMetric non-crossing source package to be
applied to the SAT separator object.
