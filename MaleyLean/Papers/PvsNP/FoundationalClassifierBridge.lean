import MaleyLean.Papers.PvsNP.SeparatorSelectorBridge

/-!
# Foundational classifier bridge for P vs NP

The A+ kernel layer already excludes independent same-domain foundational
classifiers.  This module maps a P vs NP candidate-status classifier into that
vocabulary.  The only remaining bridge is that a separating classifier is
independent/foundational in the AASC sense; once that is supplied, the existing
kernel exclusion yields selector import for the classifier route.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The foundational candidate associated to a SAT candidate-status classifier.
Only the `independentSameDomainClassifier` field is load-bearing here.
-/
def foundationalCandidateOfClassifier
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (_hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependentSameDomain :
      Prop) :
    MinimalConditionsForAdmissibleConstruction.FoundationalCandidate where
  independentGovernance := hIndependentSameDomain
  generatedFromBelow := False
  independentSameDomainClassifier := hIndependentSameDomain

/-- Evidence that a candidate-status classifier is independent and same-domain. -/
structure CnfClassifierIndependentSameDomain
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model) where
  independentSameDomain : Prop
  independentSameDomain_holds : independentSameDomain

/--
Bridge obligation: every separating candidate-status classifier is an
independent same-domain foundational classifier.
-/
def CnfSeparatingClassifierIsIndependentSameDomain
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      Nonempty (CnfClassifierIndependentSameDomain model classifier)

/-- There is an actual separating classifier in the encoded SAT candidate arena. -/
def CnfSeparatingClassifierExists
    (model : CnfEncodedCandidateModel) : Prop :=
  exists classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier

/-- A same-domain separator supplies the canonical separating classifier. -/
theorem cnfSeparatingClassifierExists_of_sameDomainSeparator
    (model : CnfEncodedCandidateModel)
    (separator : CnfSameDomainSeparator) :
    CnfSeparatingClassifierExists model :=
  Exists.intro
    (cnfClassifierOfSameDomainSeparator model separator)
    (cnfClassifierSeparates_of_sameDomainSeparator model separator)

/--
Scoped replacement for the overbroad global foundational-candidate exclusion:
no separating SAT candidate-status classifier is an independent same-domain
classifier.
-/
def CnfNoIndependentSeparatingClassifier
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      Not (Nonempty (CnfClassifierIndependentSameDomain model classifier))

/--
P vs NP-facing name for the kernel-paper object: a non-degenerate attempt
strictly below the kernel is a target-bearing, governance-equivalent regime
that fails to carry the kernel package.
-/
def CnfNonDegenerateBelowKernelAttempt
    {Act Object : Type}
    (R S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  MinimalConditionsForAdmissibleConstruction.StrictlyBelowKernel R S

/--
The non-degenerate same-regime arena: a target-bearing regime with the same
governance structure as the kernel regime.
-/
def CnfNonDegenerateSameRegimeScope
    {Act Object : Type}
    (R S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  MinimalConditionsForAdmissibleConstruction.TargetPhenomenon S /\
    MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent R S

/--
In non-degenerate same-regime scope, the kernel package is not optional: it
transfers by governance equivalence from the A+ kernel certificate.
-/
theorem cnfKernelInstantiatedByNecessity_inNonDegenerateSameRegimeScope
    {Act Object : Type}
    {R S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hScope : CnfNonDegenerateSameRegimeScope R S) :
    MinimalConditionsForAdmissibleConstruction.KernelPackage S :=
  MinimalConditionsForAdmissibleConstruction.PaperKernelPackageTransfersAcrossGovernanceEquivalenceStatement
    R S C.kernel hScope.2

/--
Equivalently: inside the non-degenerate same-regime scope, failing to instantiate
the kernel is impossible.
-/
theorem cnfKernelNotOptional_inNonDegenerateSameRegimeScope
    {Act Object : Type}
    {R S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hScope : CnfNonDegenerateSameRegimeScope R S) :
    Not (Not (MinimalConditionsForAdmissibleConstruction.KernelPackage S)) := by
  intro hNoKernel
  exact hNoKernel
    (cnfKernelInstantiatedByNecessity_inNonDegenerateSameRegimeScope
      C hScope)

/-- Governance equivalence is reflexive for any construction regime. -/
theorem cnfGovernanceEquivalent_refl
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent R R := by
  exact And.intro Iff.rfl
    (And.intro (fun _ => Iff.rfl)
      (And.intro (fun _ => Iff.rfl)
        (And.intro (fun _ => Iff.rfl) (fun _ => Iff.rfl))))

/--
Target-bearing scope is exactly the four ambient regime fields that preserve
the fixed object of construction, step eligibility, failure stability, and
governed construction use.
-/
theorem cnfTargetPhenomenon_of_regimeFields
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hTargetIdentityFixed : R.targetIdentityFixed)
    (hStepEligibilityFixed : R.stepEligibilityFixed)
    (hActTimeFailureStable : R.actTimeFailureStable)
    (hGovernedConstructionUse : R.governedConstructionUse) :
    MinimalConditionsForAdmissibleConstruction.TargetPhenomenon R := by
  exact
    And.intro hTargetIdentityFixed
      (And.intro hStepEligibilityFixed
        (And.intro hActTimeFailureStable hGovernedConstructionUse))

/-- The A+ certificate rules out non-degenerate attempts below the kernel. -/
theorem cnfNoNonDegenerateBelowKernelAttempt_of_aPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R) :
    forall S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object,
      Not (CnfNonDegenerateBelowKernelAttempt R S) := by
  intro S hBelow
  exact C.noBelowKernel S hBelow

/--
A foundational candidate is kernel-scoped when any claimed generation from
below is witnessed by an actual strictly-below-kernel construction regime.
-/
def CnfKernelScopedFoundationalCandidate
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate) :
    Prop :=
  Q.generatedFromBelow ->
    exists S : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object,
      CnfNonDegenerateBelowKernelAttempt R S

/--
The A+ kernel certificate blocks generation from below for kernel-scoped
foundational candidates.
-/
theorem cnfNoGeneratedFromBelow_of_aPlusCertificate_and_kernelScopedCandidate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hScoped : CnfKernelScopedFoundationalCandidate R Q) :
    Not Q.generatedFromBelow := by
  intro hGenerated
  rcases hScoped hGenerated with ⟨S, hBelow⟩
  exact C.noBelowKernel S hBelow

/--
Nonvacuous kernel scope: the candidate is not merely scoped by an implication
with false antecedent; it carries actual generated-from-below content.
-/
def CnfNonvacuousKernelScopedFoundationalCandidate
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate) :
    Prop :=
  CnfKernelScopedFoundationalCandidate R Q /\ Q.generatedFromBelow

/--
The repaired kernel-scoped no-independent predicate. Candidates with no
generation content are outside this quantified domain.
-/
def CnfNoIndependentNonvacuousKernelScopedFoundationalClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  forall Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate,
    CnfNonvacuousKernelScopedFoundationalCandidate R Q ->
      Not Q.independentSameDomainClassifier

/-- A+ closes the repaired nonvacuous kernel-scoped predicate directly. -/
theorem cnfNoIndependentNonvacuousKernelScopedFoundationalClassifier_of_aPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R) :
    CnfNoIndependentNonvacuousKernelScopedFoundationalClassifier R := by
  intro Q hNonvacuous _hIndependent
  exact
    (cnfNoGeneratedFromBelow_of_aPlusCertificate_and_kernelScopedCandidate
      C hNonvacuous.1)
      hNonvacuous.2

/--
The remaining scoped source needed to turn A+'s no-below theorem into a
no-independent-classifier theorem: in the nondegenerate kernel scope, an
independent same-domain foundational classifier would have to present as a
generation from below.
-/
def CnfKernelScopedIndependentForcesGenerationFromBelow
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  forall Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate,
    CnfKernelScopedFoundationalCandidate R Q ->
      Q.independentSameDomainClassifier ->
        Q.generatedFromBelow

/--
The universal scoped-generation bridge is too broad for the current
foundational-candidate encoding: a candidate can be vacuously kernel-scoped,
independent, and definitionally not generated from below.
-/
theorem cnfNoKernelScopedIndependentForcesGenerationFromBelow_currentEncoding
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Not (CnfKernelScopedIndependentForcesGenerationFromBelow R) := by
  intro hForces
  let Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate :=
    { independentGovernance := True
      generatedFromBelow := False
      independentSameDomainClassifier := True }
  have hScoped : CnfKernelScopedFoundationalCandidate R Q := by
    intro hGenerated
    cases hGenerated
  have hGenerated : Q.generatedFromBelow :=
    hForces Q hScoped True.intro
  exact hGenerated

/--
Classifier-specific replacement for the impossible universal bridge: an
independent separating SAT classifier must supply a concrete nondegenerate
below-kernel attempt.
-/
def CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        exists S :
          MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object,
            CnfNonDegenerateBelowKernelAttempt R S

/--
Nonvacuous SAT-facing foundational candidate.  This is not the original
classifier adapter, whose `generatedFromBelow` field is definitionally false;
it is the branch-local candidate used when an independent separating classifier
is being tested as a lower-bound residual.  In that regime, the same witness
loads both the independent-same-domain and generated-from-below fields.
-/
def foundationalBelowCandidateOfClassifier
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (_hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependent :
      CnfClassifierIndependentSameDomain model classifier) :
    MinimalConditionsForAdmissibleConstruction.FoundationalCandidate where
  independentGovernance := hIndependent.independentSameDomain
  generatedFromBelow := hIndependent.independentSameDomain
  independentSameDomainClassifier := hIndependent.independentSameDomain

/-- The nonvacuous SAT-facing candidate carries generated-from-below content. -/
theorem foundationalBelowCandidateOfClassifier_generatedFromBelow
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependent :
      CnfClassifierIndependentSameDomain model classifier) :
    (foundationalBelowCandidateOfClassifier
      model classifier hSeparates hIndependent).generatedFromBelow := by
  exact hIndependent.independentSameDomain_holds

/-- The same witness also carries independent-same-domain classifier content. -/
theorem foundationalBelowCandidateOfClassifier_independentSameDomainClassifier
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependent :
      CnfClassifierIndependentSameDomain model classifier) :
    (foundationalBelowCandidateOfClassifier
      model classifier hSeparates hIndependent).independentSameDomainClassifier := by
  exact hIndependent.independentSameDomain_holds

/--
The SAT below-candidate is kernel-scoped exactly when the independent separator
produces a concrete nondegenerate below-kernel attempt.
-/
theorem cnfKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependent :
      CnfClassifierIndependentSameDomain model classifier)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model) :
    CnfKernelScopedFoundationalCandidate R
      (foundationalBelowCandidateOfClassifier
        model classifier hSeparates hIndependent) := by
  intro _hGenerated
  exact hProducesBelow classifier hSeparates hIndependent

/--
The below-candidate is the precise nonvacuous SAT instantiation of the corpus
no-generation-from-below machinery.
-/
theorem cnfNonvacuousKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependent :
      CnfClassifierIndependentSameDomain model classifier)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model) :
    CnfNonvacuousKernelScopedFoundationalCandidate R
      (foundationalBelowCandidateOfClassifier
        model classifier hSeparates hIndependent) :=
  And.intro
    (cnfKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
      hSeparates hIndependent hProducesBelow)
    (foundationalBelowCandidateOfClassifier_generatedFromBelow
      model classifier hSeparates hIndependent)

/--
A concrete same-regime counterexample witness produced by an independent SAT
classifier: it stays target-bearing and governance-equivalent to the ambient
regime, but does not carry the kernel package.
-/
structure CnfClassifierSameRegimeCounterexample
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (_model : CnfEncodedCandidateModel)
    (_classifier : CnfCandidateStatusClassifier _model) where
  regime :
    MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object
  targetPhenomenon :
    MinimalConditionsForAdmissibleConstruction.TargetPhenomenon regime
  governanceEquivalent :
    MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent R regime
  noKernel :
    Not (MinimalConditionsForAdmissibleConstruction.KernelPackage regime)

/--
Fieldwise data for the same-regime counterexample.  This separates the live
mathematical work into construction of the induced regime and the three AASC
properties needed for a below-kernel attempt.
-/
structure CnfClassifierSameRegimeCounterexampleData
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (_model : CnfEncodedCandidateModel)
    (_classifier : CnfCandidateStatusClassifier _model) where
  regime :
    MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object
  targetPhenomenon :
    MinimalConditionsForAdmissibleConstruction.TargetPhenomenon regime
  governanceEquivalent :
    MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent R regime
  noKernel :
    Not (MinimalConditionsForAdmissibleConstruction.KernelPackage regime)

/--
Classifier-induced regime provider.  This names only the regime construction;
the target/governance/no-kernel proofs are separate obligations below.
-/
structure CnfClassifierInducedRegime
    {Act Object : Type}
    (_R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (_model : CnfEncodedCandidateModel)
    (_classifier : CnfCandidateStatusClassifier _model) where
  regime :
    MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object

/-- The induced regime is target-bearing. -/
def CnfClassifierInducedRegimeTargetPhenomenon
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (induced : CnfClassifierInducedRegime R model classifier) : Prop :=
  MinimalConditionsForAdmissibleConstruction.TargetPhenomenon induced.regime

/-- The induced regime is governance-equivalent to the ambient regime. -/
def CnfClassifierInducedRegimeGovernanceEquivalent
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (induced : CnfClassifierInducedRegime R model classifier) : Prop :=
  MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent
    R induced.regime

/-- The induced regime does not carry the kernel package. -/
def CnfClassifierInducedRegimeNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (induced : CnfClassifierInducedRegime R model classifier) : Prop :=
  Not (MinimalConditionsForAdmissibleConstruction.KernelPackage induced.regime)

/-- Field obligations for a fixed classifier-induced regime. -/
structure CnfClassifierInducedRegimeFieldProofs
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (induced : CnfClassifierInducedRegime R model classifier) where
  targetPhenomenon :
    CnfClassifierInducedRegimeTargetPhenomenon induced
  governanceEquivalent :
    CnfClassifierInducedRegimeGovernanceEquivalent induced
  noKernel :
    CnfClassifierInducedRegimeNoKernel induced

/--
An induced regime already scoped to the non-degenerate same-regime arena.
This bundles construction with target and governance; the remaining separate
load-bearing field is failure to carry the kernel package.
-/
structure CnfClassifierSameRegimeInducedRegime
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (_model : CnfEncodedCandidateModel)
    (_classifier : CnfCandidateStatusClassifier _model) where
  regime :
    MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object
  targetPhenomenon :
    MinimalConditionsForAdmissibleConstruction.TargetPhenomenon regime
  governanceEquivalent :
    MinimalConditionsForAdmissibleConstruction.GovernanceEquivalent R regime

/-- The ambient regime is a same-regime induced object once it is target-bearing. -/
def CnfClassifierSameRegimeInducedRegime.self
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (hTarget :
      MinimalConditionsForAdmissibleConstruction.TargetPhenomenon R) :
    CnfClassifierSameRegimeInducedRegime R model classifier where
  regime := R
  targetPhenomenon := hTarget
  governanceEquivalent := cnfGovernanceEquivalent_refl R

/-- Forget the same-regime fields and view the object as an induced regime. -/
def CnfClassifierSameRegimeInducedRegime.toInduced
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier) :
    CnfClassifierInducedRegime R model classifier where
  regime := sameRegime.regime

/-- The same-regime induced object does not carry the kernel package. -/
def CnfClassifierSameRegimeInducedRegimeNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier) : Prop :=
  Not (MinimalConditionsForAdmissibleConstruction.KernelPackage
    sameRegime.regime)

/-- Same-regime induced object plus no-kernel proof supplies all induced fields. -/
def CnfClassifierInducedRegimeFieldProofs.ofSameRegime
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier)
    (hNoKernel :
      CnfClassifierSameRegimeInducedRegimeNoKernel sameRegime) :
    CnfClassifierInducedRegimeFieldProofs sameRegime.toInduced where
  targetPhenomenon := sameRegime.targetPhenomenon
  governanceEquivalent := sameRegime.governanceEquivalent
  noKernel := hNoKernel

/-- Induced regime plus field proofs assembles into fieldwise counterexample data. -/
def cnfClassifierSameRegimeCounterexampleData_of_inducedRegime
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (induced : CnfClassifierInducedRegime R model classifier)
    (proofs : CnfClassifierInducedRegimeFieldProofs induced) :
    CnfClassifierSameRegimeCounterexampleData R model classifier where
  regime := induced.regime
  targetPhenomenon := proofs.targetPhenomenon
  governanceEquivalent := proofs.governanceEquivalent
  noKernel := proofs.noKernel

/-- Fieldwise same-regime data assembles into the counterexample witness. -/
def cnfClassifierSameRegimeCounterexample_of_data
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (data : CnfClassifierSameRegimeCounterexampleData R model classifier) :
    CnfClassifierSameRegimeCounterexample R model classifier where
  regime := data.regime
  targetPhenomenon := data.targetPhenomenon
  governanceEquivalent := data.governanceEquivalent
  noKernel := data.noKernel

/-- A same-regime counterexample is exactly a below-kernel attempt. -/
theorem cnfBelowKernelAttempt_of_sameRegimeCounterexample
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (counterexample :
      CnfClassifierSameRegimeCounterexample R model classifier) :
    CnfNonDegenerateBelowKernelAttempt R counterexample.regime :=
  And.intro counterexample.targetPhenomenon
    (And.intro counterexample.governanceEquivalent counterexample.noKernel)

/--
Smaller live bridge: an independent separating classifier produces a concrete
same-regime counterexample witness.
-/
def CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        Nonempty (CnfClassifierSameRegimeCounterexample R model classifier)

/--
Fieldwise version of the same-regime counterexample bridge.
-/
def CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        Nonempty (CnfClassifierSameRegimeCounterexampleData R model classifier)

/--
Fully decomposed bridge: an independent separating classifier produces a
classifier-induced regime and proves the three required AASC fields for it.
-/
def CnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        exists induced : CnfClassifierInducedRegime R model classifier,
          CnfClassifierInducedRegimeFieldProofs induced

/-- First split obligation: construct the classifier-induced regime. -/
def CnfSeparatingClassifierIndependenceProducesInducedRegime
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        Nonempty (CnfClassifierInducedRegime R model classifier)

/-- Second split obligation: the induced regime is target-bearing. -/
def CnfSeparatingClassifierInducedRegimeTargetPhenomenon
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall _hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier,
    forall _hIndependent :
      CnfClassifierIndependentSameDomain model classifier,
    forall induced : CnfClassifierInducedRegime R model classifier,
      CnfClassifierInducedRegimeTargetPhenomenon induced

/-- Third split obligation: the induced regime preserves governance. -/
def CnfSeparatingClassifierInducedRegimeGovernanceEquivalent
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall _hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier,
    forall _hIndependent :
      CnfClassifierIndependentSameDomain model classifier,
    forall induced : CnfClassifierInducedRegime R model classifier,
      CnfClassifierInducedRegimeGovernanceEquivalent induced

/-- Fourth split obligation: the induced regime has no kernel package. -/
def CnfSeparatingClassifierInducedRegimeNoKernel
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall _hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier,
    forall _hIndependent :
      CnfClassifierIndependentSameDomain model classifier,
    forall induced : CnfClassifierInducedRegime R model classifier,
      CnfClassifierInducedRegimeNoKernel induced

/--
Compressed same-regime obligation: an independent separating classifier
constructs an induced regime already carrying target and governance fields.
-/
def CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfClassifierIndependentSameDomain model classifier ->
        Nonempty (CnfClassifierSameRegimeInducedRegime R model classifier)

/--
If the ambient AASC regime is already target-bearing, the same-regime induced
construction is witnessed by the ambient regime itself.
-/
theorem cnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime_of_targetPhenomenon
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hTarget :
      MinimalConditionsForAdmissibleConstruction.TargetPhenomenon R) :
    CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
      R model := by
  intro classifier _hSeparates _hIndependent
  exact
    Nonempty.intro
      (CnfClassifierSameRegimeInducedRegime.self
        (R := R)
        (model := model)
        (classifier := classifier)
        hTarget)

/--
The remaining compressed obligation: every same-regime induced regime generated
by an independent separating classifier lacks the kernel package.
-/
def CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall _hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier,
    forall _hIndependent :
      CnfClassifierIndependentSameDomain model classifier,
    forall sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier,
        CnfClassifierSameRegimeInducedRegimeNoKernel sameRegime

/--
Inside A+, a same-regime induced object necessarily carries the kernel package:
target/governance place it in the non-degenerate same-regime scope.
-/
theorem cnfKernelPackage_of_sameRegimeInduced
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier) :
    MinimalConditionsForAdmissibleConstruction.KernelPackage
      sameRegime.regime :=
  MinimalConditionsForAdmissibleConstruction.PaperKernelPackageTransfersAcrossGovernanceEquivalenceStatement
    R sameRegime.regime C.kernel sameRegime.governanceEquivalent

/-- Therefore the no-kernel field is locally contradictory on any A+ same-regime induced object. -/
theorem cnfNoKernelImpossible_for_sameRegimeInduced
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (sameRegime :
      CnfClassifierSameRegimeInducedRegime R model classifier) :
    Not (CnfClassifierSameRegimeInducedRegimeNoKernel sameRegime) := by
  intro hNoKernel
  exact hNoKernel (cnfKernelPackage_of_sameRegimeInduced C sameRegime)

/--
If an independent separating classifier produces a same-regime induced object,
then the global no-kernel field collapses that classifier immediately under A+.
-/
theorem cnfNoIndependentSeparatingClassifier_of_aPlus_and_sameRegimeInducedNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hSameRegime :
      CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
        R model)
    (hNoKernel :
      CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model) :
    CnfNoIndependentSeparatingClassifier model := by
  intro classifier hSeparates hIndependent
  cases hIndependent with
  | intro W =>
      cases hSameRegime classifier hSeparates W with
      | intro sameRegime =>
          exact
            cnfNoKernelImpossible_for_sameRegimeInduced C sameRegime
              (hNoKernel classifier hSeparates W sameRegime)

/-- No-independent classifiers contradict the existence of a separating independent classifier. -/
theorem cnfNoSeparatingClassifierExists_of_noIndependent_and_independence
    {model : CnfEncodedCandidateModel}
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not (CnfSeparatingClassifierExists model) := by
  intro hExists
  rcases hExists with ⟨classifier, hSeparates⟩
  exact hNoIndependent classifier hSeparates
    (hIndependent classifier hSeparates)

/--
The compressed same-regime induced route rules out an actual separating
classifier: if the negative branch is populated, A+ transfers the kernel to the
induced regime and contradicts the no-kernel field.
-/
theorem cnfNoSeparatingClassifierExists_of_aPlus_and_sameRegimeInducedNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hSameRegime :
      CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
        R model)
    (hNoKernel :
      CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not (CnfSeparatingClassifierExists model) :=
  cnfNoSeparatingClassifierExists_of_noIndependent_and_independence
    (cnfNoIndependentSeparatingClassifier_of_aPlus_and_sameRegimeInducedNoKernel
      C hSameRegime hNoKernel)
    hIndependent

/-- Therefore the compressed same-regime induced route rules out same-domain separators. -/
theorem cnfNoSameDomainSeparator_of_aPlus_and_sameRegimeInducedNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hSameRegime :
      CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
        R model)
    (hNoKernel :
      CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not CnfSameDomainSeparator := by
  intro hSeparator
  exact
    (cnfNoSeparatingClassifierExists_of_aPlus_and_sameRegimeInducedNoKernel
      C hSameRegime hNoKernel hIndependent)
      (cnfSeparatingClassifierExists_of_sameDomainSeparator
        model hSeparator)

/--
Target-bearing same-regime scope removes the construction source entirely:
any same-domain separator gives the canonical classifier, SAT independence gives
the witness, and the self-induced regime is the ambient regime `R`.  The
no-kernel branch then contradicts the A+ kernel package.
-/
theorem cnfNoSameDomainSeparator_of_aPlus_targetPhenomenon_and_sameRegimeInducedNoKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hTarget :
      MinimalConditionsForAdmissibleConstruction.TargetPhenomenon R)
    (hNoKernel :
      CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not CnfSameDomainSeparator := by
  intro hSeparator
  let classifier := cnfClassifierOfSameDomainSeparator model hSeparator
  have hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier :=
    cnfClassifierSeparates_of_sameDomainSeparator model hSeparator
  cases hIndependent classifier hSeparates with
  | intro independent =>
      let sameRegime :
          CnfClassifierSameRegimeInducedRegime R model classifier :=
        CnfClassifierSameRegimeInducedRegime.self
          (R := R)
          (model := model)
          (classifier := classifier)
          hTarget
      exact
        (hNoKernel classifier hSeparates independent sameRegime)
          C.kernel

/-- Same-regime induced obligations assemble into the induced-regime-with-fields bridge. -/
theorem cnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields_of_sameRegimeInduced
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hSameRegime :
      CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
        R model)
    (hNoKernel :
      CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model) :
    CnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields
      R model := by
  intro classifier hSeparates hIndependent
  cases hSameRegime classifier hSeparates hIndependent with
  | intro sameRegime =>
      exact
        Exists.intro sameRegime.toInduced
          (CnfClassifierInducedRegimeFieldProofs.ofSameRegime
            sameRegime
            (hNoKernel classifier hSeparates hIndependent sameRegime))

/-- Split obligations assemble into the induced-regime-with-fields bridge. -/
theorem cnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields_of_splitObligations
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hRegime :
      CnfSeparatingClassifierIndependenceProducesInducedRegime R model)
    (hTarget :
      CnfSeparatingClassifierInducedRegimeTargetPhenomenon R model)
    (hGovernance :
      CnfSeparatingClassifierInducedRegimeGovernanceEquivalent R model)
    (hNoKernel :
      CnfSeparatingClassifierInducedRegimeNoKernel R model) :
    CnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields
      R model := by
  intro classifier hSeparates hIndependent
  rcases hRegime classifier hSeparates hIndependent with ⟨induced⟩
  exact
    ⟨induced,
      { targetPhenomenon :=
          hTarget classifier hSeparates hIndependent induced
        governanceEquivalent :=
          hGovernance classifier hSeparates hIndependent induced
        noKernel :=
          hNoKernel classifier hSeparates hIndependent induced }⟩

/-- The decomposed induced-regime bridge supplies the data-level bridge. -/
theorem cnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData_of_inducedRegime
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hInduced :
      CnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields
        R model) :
    CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData
      R model := by
  intro classifier hSeparates hIndependent
  rcases hInduced classifier hSeparates hIndependent with
    ⟨induced, proofs⟩
  exact
    ⟨cnfClassifierSameRegimeCounterexampleData_of_inducedRegime
      induced proofs⟩

/-- The fieldwise bridge supplies the same-regime counterexample bridge. -/
theorem cnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample_of_data
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hData :
      CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData
        R model) :
    CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample
      R model := by
  intro classifier hSeparates hIndependent
  rcases hData classifier hSeparates hIndependent with ⟨data⟩
  exact ⟨cnfClassifierSameRegimeCounterexample_of_data data⟩

/--
The same-regime counterexample bridge supplies the below-kernel-attempt bridge.
-/
theorem cnfSeparatingClassifierIndependenceProducesBelowKernelAttempt_of_sameRegimeCounterexample
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hCounterexample :
      CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample
        R model) :
    CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model := by
  intro classifier hSeparates hIndependent
  rcases hCounterexample classifier hSeparates hIndependent with
    ⟨counterexample⟩
  exact
    ⟨counterexample.regime,
      cnfBelowKernelAttempt_of_sameRegimeCounterexample counterexample⟩

/--
Kernel-scoped version of the A+ no-independent-classifier condition.  Unlike
the dead global condition, this only quantifies over candidates whose generation
claim is interpreted inside the non-degenerate kernel scope.
-/
def CnfNoIndependentKernelScopedFoundationalClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  forall Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate,
    CnfKernelScopedFoundationalCandidate R Q ->
      Not Q.independentSameDomainClassifier

/--
The current kernel-scoped no-independent predicate is still too broad: because
kernel scope is represented as an implication out of `generatedFromBelow`, a
candidate with `generatedFromBelow := False` is scoped vacuously.
-/
theorem cnfNoIndependentKernelScopedFoundationalClassifier_currentEncoding_inconsistent
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Not (CnfNoIndependentKernelScopedFoundationalClassifier R) := by
  intro hNoScoped
  let Q : MinimalConditionsForAdmissibleConstruction.FoundationalCandidate :=
    { independentGovernance := True
      generatedFromBelow := False
      independentSameDomainClassifier := True }
  have hScoped : CnfKernelScopedFoundationalCandidate R Q := by
    intro hGenerated
    cases hGenerated
  exact hNoScoped Q hScoped True.intro

/--
A+ plus the scoped generation bridge closes the kernel-scoped
no-independent-classifier source.
-/
theorem cnfNoIndependentKernelScopedFoundationalClassifier_of_aPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hForcesGeneration :
      CnfKernelScopedIndependentForcesGenerationFromBelow R) :
    CnfNoIndependentKernelScopedFoundationalClassifier R := by
  intro Q hScoped hIndependent
  exact
    (cnfNoGeneratedFromBelow_of_aPlusCertificate_and_kernelScopedCandidate
      C hScoped)
      (hForcesGeneration Q hScoped hIndependent)

/--
Compact source package for deriving the kernel-scoped no-independent theorem
from A+ and the scoped generation bridge.
-/
structure CnfNoIndependentKernelScopedFoundationalSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentForcesGeneration :
    CnfKernelScopedIndependentForcesGenerationFromBelow R

/-- The source package supplies the kernel-scoped no-independent theorem. -/
theorem cnfNoIndependentKernelScopedFoundationalClassifier_of_sourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (package : CnfNoIndependentKernelScopedFoundationalSourcePackage R) :
    CnfNoIndependentKernelScopedFoundationalClassifier R :=
  cnfNoIndependentKernelScopedFoundationalClassifier_of_aPlusCertificate
    package.aPlus
    package.independentForcesGeneration

/--
A+ plus the classifier-specific below-kernel bridge rules out independent
separating SAT classifiers.
-/
theorem cnfNoIndependentSeparatingClassifier_of_aPlusCertificate_and_belowAttemptBridge
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model) :
    CnfNoIndependentSeparatingClassifier model := by
  intro classifier hSeparates hIndependent
  rcases hIndependent with ⟨W⟩
  rcases hProducesBelow classifier hSeparates W with ⟨S, hBelow⟩
  exact C.noBelowKernel S hBelow

/-- Source package for the classifier-specific no-independent route. -/
structure CnfNoIndependentSeparatingClassifierSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesBelow :
    CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model

/-- The classifier-specific source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_sourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfNoIndependentSeparatingClassifierSourcePackage R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_aPlusCertificate_and_belowAttemptBridge
    package.aPlus
    package.independentProducesBelow

/-- Source package using the finer same-regime counterexample bridge. -/
structure CnfNoIndependentSeparatingClassifierSameRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesCounterexample :
    CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample R model

/-- The same-regime source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_sameRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSameRegimeSourcePackage R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_aPlusCertificate_and_belowAttemptBridge
    package.aPlus
    (cnfSeparatingClassifierIndependenceProducesBelowKernelAttempt_of_sameRegimeCounterexample
      package.independentProducesCounterexample)

/-- Source package using fieldwise same-regime counterexample data. -/
structure CnfNoIndependentSeparatingClassifierSameRegimeDataSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesCounterexampleData :
    CnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData
      R model

/-- The fieldwise source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_sameRegimeDataSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSameRegimeDataSourcePackage
        R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_sameRegimeSourcePackage
    { aPlus := package.aPlus
      independentProducesCounterexample :=
        cnfSeparatingClassifierIndependenceProducesSameRegimeCounterexample_of_data
          package.independentProducesCounterexampleData }

/-- Source package using the decomposed induced-regime field bridge. -/
structure CnfNoIndependentSeparatingClassifierInducedRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesInducedRegime :
    CnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields
      R model

/-- The induced-regime source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_inducedRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierInducedRegimeSourcePackage
        R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_sameRegimeDataSourcePackage
    { aPlus := package.aPlus
      independentProducesCounterexampleData :=
        cnfSeparatingClassifierIndependenceProducesSameRegimeCounterexampleData_of_inducedRegime
          package.independentProducesInducedRegime }

/-- Source package using the compressed same-regime induced-regime bridge. -/
structure CnfNoIndependentSeparatingClassifierSameRegimeInducedSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesSameRegimeInduced :
    CnfSeparatingClassifierIndependenceProducesSameRegimeInducedRegime
      R model
  sameRegimeInducedNoKernel :
    CnfSeparatingClassifierSameRegimeInducedRegimeNoKernel R model

/-- The same-regime induced source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_sameRegimeInducedSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSameRegimeInducedSourcePackage
        R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_aPlus_and_sameRegimeInducedNoKernel
    package.aPlus
    package.independentProducesSameRegimeInduced
    package.sameRegimeInducedNoKernel

/-- The same-regime induced source package rules out an actual separating classifier. -/
theorem cnfNoSeparatingClassifierExists_of_sameRegimeInducedSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSameRegimeInducedSourcePackage
        R model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not (CnfSeparatingClassifierExists model) :=
  cnfNoSeparatingClassifierExists_of_aPlus_and_sameRegimeInducedNoKernel
    package.aPlus
    package.independentProducesSameRegimeInduced
    package.sameRegimeInducedNoKernel
    hIndependent

/-- The same-regime induced source package rules out same-domain separators. -/
theorem cnfNoSameDomainSeparator_of_sameRegimeInducedSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSameRegimeInducedSourcePackage
        R model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    Not CnfSameDomainSeparator :=
  cnfNoSameDomainSeparator_of_aPlus_and_sameRegimeInducedNoKernel
    package.aPlus
    package.independentProducesSameRegimeInduced
    package.sameRegimeInducedNoKernel
    hIndependent

/-- Source package using the four split induced-regime obligations. -/
structure CnfNoIndependentSeparatingClassifierSplitRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  inducedRegime :
    CnfSeparatingClassifierIndependenceProducesInducedRegime R model
  targetPhenomenon :
    CnfSeparatingClassifierInducedRegimeTargetPhenomenon R model
  governanceEquivalent :
    CnfSeparatingClassifierInducedRegimeGovernanceEquivalent R model
  noKernel :
    CnfSeparatingClassifierInducedRegimeNoKernel R model

/-- The split-regime source package supplies no independent separator. -/
theorem cnfNoIndependentSeparatingClassifier_of_splitRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfNoIndependentSeparatingClassifierSplitRegimeSourcePackage
        R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_inducedRegimeSourcePackage
    { aPlus := package.aPlus
      independentProducesInducedRegime :=
        cnfSeparatingClassifierIndependenceProducesInducedRegimeWithFields_of_splitObligations
          package.inducedRegime
          package.targetPhenomenon
          package.governanceEquivalent
          package.noKernel }

/--
The foundational candidate extracted from a SAT classifier is kernel-scoped:
its `generatedFromBelow` component is definitionally false.
-/
theorem cnfKernelScopedCandidate_of_classifier
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier)
    (hIndependentSameDomain : Prop) :
    CnfKernelScopedFoundationalCandidate R
      (foundationalCandidateOfClassifier
        model classifier hSeparates hIndependentSameDomain) := by
  intro hGenerated
  cases hGenerated

/--
Kernel-scoped foundational exclusion supplies the SAT-scoped
no-independent-separating-classifier source.
-/
theorem
    cnfNoIndependentSeparatingClassifier_of_noIndependentKernelScopedFoundationalClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R) :
    CnfNoIndependentSeparatingClassifier model := by
  intro classifier hSeparates hIndependent
  rcases hIndependent with ⟨W⟩
  let Q :=
    foundationalCandidateOfClassifier
      model classifier hSeparates W.independentSameDomain
  have hScoped : CnfKernelScopedFoundationalCandidate R Q :=
    cnfKernelScopedCandidate_of_classifier
      (R := R) model classifier hSeparates W.independentSameDomain
  have hQ : Q.independentSameDomainClassifier := W.independentSameDomain_holds
  exact hNoScoped Q hScoped hQ

/--
The nonvacuous repaired kernel route supplies the SAT-local exclusion once a
separating classifier is known to produce an actual below-kernel attempt.
-/
theorem
    cnfNoIndependentSeparatingClassifier_of_noIndependentNonvacuousKernelScopedFoundationalClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel)
    (hNoScoped :
      CnfNoIndependentNonvacuousKernelScopedFoundationalClassifier R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model) :
    CnfNoIndependentSeparatingClassifier model := by
  intro classifier hSeparates hIndependent
  cases hIndependent with
  | intro W =>
      let Q :=
        foundationalBelowCandidateOfClassifier
          model classifier hSeparates W
      have hScoped : CnfKernelScopedFoundationalCandidate R Q := by
        exact
          cnfKernelScopedFoundationalBelowCandidate_of_belowKernelAttempt
            hSeparates W hProducesBelow
      have hNonvacuous :
          CnfNonvacuousKernelScopedFoundationalCandidate R Q :=
        And.intro hScoped
          (foundationalBelowCandidateOfClassifier_generatedFromBelow
            model classifier hSeparates W)
      have hQ : Q.independentSameDomainClassifier :=
        foundationalBelowCandidateOfClassifier_independentSameDomainClassifier
          model classifier hSeparates W
      exact hNoScoped Q hNonvacuous hQ

/--
A+ plus the classifier-specific below-kernel bridge is the concrete
nonvacuous-kernel formulation of the SAT-local no-independent theorem.
-/
theorem
    cnfNoIndependentSeparatingClassifier_of_aPlus_and_nonvacuousKernelScope
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model) :
    CnfNoIndependentSeparatingClassifier model :=
  cnfNoIndependentSeparatingClassifier_of_noIndependentNonvacuousKernelScopedFoundationalClassifier
    R
    model
    (cnfNoIndependentNonvacuousKernelScopedFoundationalClassifier_of_aPlusCertificate
      C)
    hProducesBelow

/--
The global AASC no-independent-classifier theorem is stronger than the
kernel-scoped version: restricting its quantifier to kernel-scoped candidates
immediately yields the scoped exclusion.
-/
theorem
    cnfNoIndependentKernelScopedFoundationalClassifier_of_noIndependentClassifier
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier) :
    CnfNoIndependentKernelScopedFoundationalClassifier R := by
  intro Q _hScoped hIndependent
  exact hNoIndependent Q hIndependent

/--
The AASC kernel exclusion of independent same-domain foundational classifiers
turns a separating candidate-status classifier into contradiction, hence into
boundary-selector import under the P vs NP-facing boundary alias.
-/
theorem cnfClassifierWouldImportSelector_of_noIndependentClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    CnfCandidateClassifierWouldImportSelector R model := by
  intro classifier hSeparates hBoundary
  rcases hIndependent classifier hSeparates with ⟨W⟩
  let Q :=
    foundationalCandidateOfClassifier
      model classifier hSeparates W.independentSameDomain
  have hQ : Q.independentSameDomainClassifier := W.independentSameDomain_holds
  exact hNoIndependent Q hQ

/--
SAT-scoped classifier exclusion turns the independent-classifier bridge into
selector import without quantifying over arbitrary foundational triples.
-/
theorem cnfClassifierWouldImportSelector_of_noIndependentSeparatingClassifier
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel)
    (hNoIndependent :
      CnfNoIndependentSeparatingClassifier model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model) :
    CnfCandidateClassifierWouldImportSelector R model := by
  intro classifier hSeparates
  exfalso
  exact hNoIndependent classifier hSeparates
    (hIndependent classifier hSeparates)

/--
Under the fixed ametric/bivalent boundary, no-independent-classifier A+ rule,
and the bridge that separating SAT classifiers are independent same-domain
classifiers, the endpoint fork collapses to the positive endpoint.
-/
theorem cnfPositiveEndpoint_of_noIndependentClassifier
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_classifierImport
    boundary
    (cnfClassifierWouldImportSelector_of_noIndependentClassifier
      R model hNoIndependent hIndependent)
    hEndpoint

/--
Scoped endpoint collapse using only the SAT-local independent-classifier
exclusion.
-/
theorem cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      CnfNoIndependentSeparatingClassifier model)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_classifierImport
    boundary
    (cnfClassifierWouldImportSelector_of_noIndependentSeparatingClassifier
      R model hNoIndependent hIndependent)
    hEndpoint

/--
Endpoint collapse from the revived kernel-scoped foundational classifier
condition.
-/
theorem cnfPositiveEndpoint_of_noIndependentKernelScopedFoundationalClassifier
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hIndependent :
      CnfSeparatingClassifierIsIndependentSameDomain model)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    boundary
    (cnfNoIndependentSeparatingClassifier_of_noIndependentKernelScopedFoundationalClassifier
      R model hNoScoped)
    hIndependent
    hEndpoint

/--
Compact package for the A+ sourced classifier-collapse route.
-/
structure CnfPositiveEndpointFoundationalCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentClassifier :
    MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/-- The A+ sourced collapse package yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_foundationalCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointFoundationalCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentClassifier
    package.boundary
    package.noIndependentClassifier
    package.separatingClassifierIndependent
    package.endpointImage

/-- Compact package for the SAT-scoped classifier-collapse route. -/
structure CnfPositiveEndpointScopedClassifierCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSeparatingClassifier :
    CnfNoIndependentSeparatingClassifier model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/-- The scoped classifier-collapse package yields the positive endpoint. -/
theorem cnfPositiveEndpoint_of_scopedClassifierCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointScopedClassifierCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    package.noIndependentSeparatingClassifier
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus the classifier-specific below-attempt
bridge.
-/
structure CnfPositiveEndpointClassifierBelowAttemptSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierSourcePackage R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The classifier-specific below-attempt source package yields the positive
endpoint.
-/
theorem cnfPositiveEndpoint_of_classifierBelowAttemptSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointClassifierBelowAttemptSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_sourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus the same-regime counterexample bridge.
-/
structure CnfPositiveEndpointClassifierSameRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierSameRegimeSourcePackage R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The same-regime counterexample source package yields the positive endpoint.
-/
theorem cnfPositiveEndpoint_of_classifierSameRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointClassifierSameRegimeSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_sameRegimeSourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus fieldwise same-regime counterexample
data.
-/
structure CnfPositiveEndpointClassifierSameRegimeDataSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierSameRegimeDataSourcePackage R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The fieldwise same-regime data source package yields the positive endpoint.
-/
theorem cnfPositiveEndpoint_of_classifierSameRegimeDataSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointClassifierSameRegimeDataSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_sameRegimeDataSourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus the decomposed induced-regime field
bridge.
-/
structure CnfPositiveEndpointClassifierInducedRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierInducedRegimeSourcePackage R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The induced-regime field source package yields the positive endpoint.
-/
theorem cnfPositiveEndpoint_of_classifierInducedRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointClassifierInducedRegimeSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_inducedRegimeSourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus the compressed same-regime induced
bridge.
-/
structure CnfPositiveEndpointClassifierSameRegimeInducedSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierSameRegimeInducedSourcePackage
      R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/-- The same-regime induced source package yields the positive endpoint. -/
theorem cnfPositiveEndpoint_of_classifierSameRegimeInducedSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointClassifierSameRegimeInducedSourcePackage
        R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_sameRegimeInducedSourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/--
Compact endpoint package using A+ plus the four split induced-regime
obligations.
-/
structure CnfPositiveEndpointClassifierSplitRegimeSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentSource :
    CnfNoIndependentSeparatingClassifierSplitRegimeSourcePackage R model
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/-- The split induced-regime source package yields the positive endpoint. -/
theorem cnfPositiveEndpoint_of_classifierSplitRegimeSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointClassifierSplitRegimeSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentSeparatingClassifier
    package.boundary
    (cnfNoIndependentSeparatingClassifier_of_splitRegimeSourcePackage
      package.noIndependentSource)
    package.separatingClassifierIndependent
    package.endpointImage

/-- Compact package for the kernel-scoped foundational classifier route. -/
structure CnfPositiveEndpointKernelScopedFoundationalPackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentKernelScoped :
    CnfNoIndependentKernelScopedFoundationalClassifier R
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The kernel-scoped foundational package yields the positive endpoint through the
SAT-scoped classifier route.
-/
theorem cnfPositiveEndpoint_of_kernelScopedFoundationalPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointKernelScopedFoundationalPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentKernelScopedFoundationalClassifier
    package.boundary
    package.noIndependentKernelScoped
    package.separatingClassifierIndependent
    package.endpointImage

/-- Compact endpoint package using the A+ plus scoped-generation source shape. -/
structure CnfPositiveEndpointKernelScopedFoundationalSourcePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  kernelScopedSource :
    CnfNoIndependentKernelScopedFoundationalSourcePackage R
  separatingClassifierIndependent :
    CnfSeparatingClassifierIsIndependentSameDomain model

/--
The A+ plus scoped-generation source package yields the positive endpoint.
-/
theorem cnfPositiveEndpoint_of_kernelScopedFoundationalSourcePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointKernelScopedFoundationalSourcePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentKernelScopedFoundationalClassifier
    package.boundary
    (cnfNoIndependentKernelScopedFoundationalClassifier_of_sourcePackage
      package.kernelScopedSource)
    package.separatingClassifierIndependent
    package.endpointImage

end PvsNP
end Papers
end MaleyLean
