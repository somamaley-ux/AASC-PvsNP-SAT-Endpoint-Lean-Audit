import MaleyLean.Papers.PvsNP.AmetricBoundary

/-!
# Horizon analogy for the P vs NP ametric boundary

The AASC horizon papers treat a permanent horizon as inadmissible when it is a
standing sink: standing crosses a boundary and has no future admissible image.
The P vs NP analogue is an external resource/infinity shadow that tries to hide
the endpoint status of a SAT candidate.  Such a shadow is harmless only if it
has endpoint anchor transport: it returns as an actual direct gate or as an
actual separator/counterexample lower bound.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The two Clay-facing endpoint images available to the bounded-CNF SAT scaffold:
either a direct polynomial-time SAT object is present, or a counterexample
lower bound separates every such candidate.
-/
def CnfEndpointAnchorTransport : Prop :=
  CnfSATInPolyTime \/ CnfCounterexampleLowerBound

/--
A P vs NP shadow horizon is any external operational shadow considered as a
candidate hiding place for endpoint status.
-/
structure CnfShadowHorizon
    (model : CnfEncodedCandidateModel) where
  shadow : CnfExternalOperationalShadow model
  permanent : Prop
  permanent_holds : permanent

/--
A shadow horizon is a standing sink exactly when its external bookkeeping has no
endpoint image in the bounded-CNF SAT scaffold.
-/
def CnfShadowStandingSink
    {model : CnfEncodedCandidateModel}
    (_horizon : CnfShadowHorizon model) : Prop :=
  Not CnfEndpointAnchorTransport

/--
The P vs NP analogue of horizon instability: a permanent shadow horizon is
admissible only if endpoint anchor transport is supplied.  The theorem is stated
as the clean AASC rule, not as a proof of the missing separator.
-/
def CnfNoPermanentShadowHorizon
    (model : CnfEncodedCandidateModel) : Prop :=
  forall horizon : CnfShadowHorizon model,
    Not (CnfShadowStandingSink horizon)

/--
A shadowed antichecker gives endpoint anchor transport through the separator
branch.
-/
theorem cnfEndpointAnchorTransport_of_shadowedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfEndpointAnchorTransport :=
  Or.inr (counterexampleLowerBound_of_shadowedAntichecker model package)

/--
Once a shadowed antichecker is supplied, every permanent shadow horizon has a
non-sink endpoint image.
-/
theorem cnfNoPermanentShadowHorizon_of_shadowedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfNoPermanentShadowHorizon model := by
  intro horizon hSink
  exact hSink (cnfEndpointAnchorTransport_of_shadowedAntichecker model package)

/--
At a fixed ametric/bivalent boundary, the horizon analogy contributes no third
status: the shadow must return through endpoint anchor transport, and the
boundary package remains unchanged.
-/
theorem cnfAmetricBoundary_with_noPermanentShadowHorizon
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfAmetricBoundary R /\
      CnfBoundaryBivalence R /\
      CnfNoPermanentShadowHorizon model :=
  And.intro boundary.ametricBoundary
    (And.intro boundary.bivalence
      (cnfNoPermanentShadowHorizon_of_shadowedAntichecker model package))

end PvsNP
end Papers
end MaleyLean
