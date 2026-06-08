import MaleyLean.Papers.PvsNP.OperationalShadow
import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusAudit

/-!
# The ametric boundary for the P vs NP operational shadow

The P vs NP scaffold may talk externally about finite codes, traces, time, and
space, but those observations are not AASC primitives.  The AASC-facing boundary
condition is the existing kernel-paper obligation `NoBoundarySelectorImport`.

This module makes the compatibility point explicit: operational shadows can be
carried as external evidence, but they cannot import a boundary selector.  The
only way into the SAT endpoint is still to forget the shadow and provide the
separating CNF formula.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- The AASC ametric boundary condition, specialized as a P vs NP-facing alias. -/
abbrev CnfAmetricBoundary
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) : Prop :=
  MinimalConditionsForAdmissibleConstruction.NoBoundarySelectorImport R

/-- The bivalence condition induced by a fixed AASC admissibility boundary. -/
abbrev CnfBoundaryBivalence
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) : Prop :=
  MinimalConditionsForAdmissibleConstruction.AdmissibilityBivalent R

/--
An interface recording that a P vs NP encoded-candidate model is being used
under an already fixed AASC ametric boundary.
-/
structure CnfAmetricBoundaryInterface
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBoundary R
  shadowExternalOnly :
    forall _shadow : CnfExternalOperationalShadow model, CnfAmetricBoundary R

/--
A fixed ametric boundary package.  This is the form in which bivalence is
available: not from resource shadows, and not from the naked no-selector fact
alone, but from the fixed AASC boundary carrying both non-parameterization and
the binary admissibility split.
-/
structure CnfAmetricBivalentBoundaryInterface
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundaryFixed : R.boundaryFixed
  ametricBoundary : CnfAmetricBoundary R
  bivalence : CnfBoundaryBivalence R
  shadowExternalOnly :
    forall _shadow : CnfExternalOperationalShadow model,
      R.boundaryFixed /\ CnfAmetricBoundary R /\ CnfBoundaryBivalence R

/--
Any external operational shadow preserves the already supplied ametric boundary:
it contributes no boundary selector.
-/
theorem cnfAmetricBoundary_preserved_by_shadow
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hBoundary : CnfAmetricBoundary R)
    (_shadow : CnfExternalOperationalShadow model) :
    CnfAmetricBoundary R :=
  hBoundary

/-- Build the P vs NP boundary interface from an A+ audit certificate. -/
def CnfAmetricBoundaryInterface.ofAPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (model : CnfEncodedCandidateModel) :
    CnfAmetricBoundaryInterface R model where
  boundary := C.requires_ametric_boundary
  shadowExternalOnly := fun shadow =>
    cnfAmetricBoundary_preserved_by_shadow C.requires_ametric_boundary shadow

/-- Build the fixed ametric/bivalent boundary interface from an A+ audit certificate. -/
def CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (model : CnfEncodedCandidateModel) :
    CnfAmetricBivalentBoundaryInterface R model where
  boundaryFixed := C.requires_bivalence.1
  ametricBoundary := C.requires_ametric_boundary
  bivalence := C.requires_bivalence.2
  shadowExternalOnly := fun _shadow =>
    And.intro C.requires_bivalence.1
      (And.intro C.requires_ametric_boundary C.requires_bivalence.2)

/--
An A+ audit certificate supplies the fixed ametric/bivalent boundary interface.
This is the dependency used by the reduced SAT operator route to avoid treating
the boundary interface as an independent primitive input.
-/
theorem cnfAmetricBivalentBoundaryInterface_nonempty_of_aPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel} :
    Nonempty
        (MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate
          R) ->
      Nonempty (CnfAmetricBivalentBoundaryInterface R model) := by
  rintro ⟨C⟩
  exact ⟨CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model⟩

/-- Bivalence is read from the fixed ametric boundary package. -/
theorem cnfBivalence_of_ametricBoundary
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model) :
    CnfBoundaryBivalence R :=
  boundary.bivalence

/-- A fixed ametric/bivalent boundary still exposes the no-selector condition. -/
theorem cnfAmetricBoundary_of_bivalentBoundary
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model) :
    CnfAmetricBoundary R :=
  boundary.ametricBoundary

/--
The ametric boundary and shadowed anticheckers compose only after the shadow is
forgotten: the boundary fact is retained, and the antichecker supplies the same
counterexample lower bound as before.
-/
theorem cnfAmetricCounterexampleLowerBound_of_shadowedAntichecker
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBoundaryInterface R model)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfAmetricBoundary R /\ CnfCounterexampleLowerBound :=
  And.intro
    (boundary.shadowExternalOnly package.shadow)
    (counterexampleLowerBound_of_shadowedAntichecker model package)

/--
At the ametric boundary, resource shadows are admissible only as external
bookkeeping; the endpoint still follows from the forgotten antichecker.
-/
theorem noCnfMachineTarget_at_ametricBoundary
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (_boundary : CnfAmetricBoundaryInterface R model)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_shadowedAntichecker model package

end PvsNP
end Papers
end MaleyLean
