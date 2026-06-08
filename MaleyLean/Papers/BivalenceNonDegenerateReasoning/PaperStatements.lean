import MaleyLean.Papers.BivalenceNonDegenerateReasoning.Verbatim.TheoremRegister
import MaleyLean.PaperStatements
import MaleyLean.PaperStatementsConstructive
import MaleyLean.ATSPaperStatements
import MaleyLean.GodelPaperStatements
import MaleyLean.Papers.UnusSolusPossibilisEst.ManuscriptTheorems

namespace MaleyLean
namespace Papers
namespace BivalenceNonDegenerateReasoning

/--
A lightweight same-scope governance package keyed to the manuscript's local
theorem ladder.
-/
structure GovernanceSystem (Act : Type) where
  standing : Act -> Prop
  licensedContinuation : Act -> Act -> Prop
  governanceBearingNonDegenerateUse : Prop
  reference : Prop
  standingPersistence : Prop
  irreversibility : Prop
  priorGate : Prop
  failClosed : Prop
  blocksSilentRedescription : Prop
  scopeIntegrity : Prop

def KernelRoles
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  R.reference /\ R.standingPersistence /\ R.irreversibility

def AASCClass
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  R.priorGate /\
  R.blocksSilentRedescription /\
  R.scopeIntegrity /\
  R.failClosed

def NoSameActRepair
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  forall a : Act,
    forall T : Act -> Act,
      Not (R.standing a) ->
      T a = a ->
      Not (R.standing (T a))

def NoSecondSameScopeAdmissibilityInvariant
    {Act : Type}
    (R : GovernanceSystem Act)
    (I : Act -> Prop) : Prop :=
  forall a : Act, I a <-> R.standing a

inductive GovernanceRole where
  | anchor
  | tensor
  | skin
deriving DecidableEq, Repr

def SameScopeRoleExhaustion : Prop :=
  forall r : GovernanceRole,
    r = GovernanceRole.anchor \/
    r = GovernanceRole.tensor \/
    r = GovernanceRole.skin

def StandingConservation
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  NoSameActRepair R /\ R.priorGate /\ R.failClosed

def SameInferentialLife
    {Act : Type}
    (R : GovernanceSystem Act)
    (a b : Act) : Prop :=
  (R.standing a <-> R.standing b) /\
  (forall c : Act, R.licensedContinuation a c <-> R.licensedContinuation b c)

def InferentialLifeExhausted
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  forall a b : Act, SameInferentialLife R a b -> SameInferentialLife R a b

def GovernanceRelevantDifference
    {Act : Type}
    (R : GovernanceSystem Act)
    (a b : Act) : Prop :=
  Not (SameInferentialLife R a b)

def ClosureRelevanceTransmission
    {Act : Type}
    (R : GovernanceSystem Act) : Prop :=
  forall a b : Act,
    GovernanceRelevantDifference R a b ->
    GovernanceRelevantDifference R a b

inductive GovernanceLocus where
  | verdictStability
  | actIdentity
  | evaluationOrder
  | reversibility
  | scopeIntegrity
deriving DecidableEq, Repr

def GovernanceLociExhausted : Prop :=
  forall l : GovernanceLocus,
    l = GovernanceLocus.verdictStability \/
    l = GovernanceLocus.actIdentity \/
    l = GovernanceLocus.evaluationOrder \/
    l = GovernanceLocus.reversibility \/
    l = GovernanceLocus.scopeIntegrity

inductive FailureFamily where
  | silentRedescription
  | identityDrift
  | deferredValidation
  | postHocRehabilitation
  | scopeOrEnvelopeDrift
deriving DecidableEq, Repr

def FailureFamiliesExhausted : Prop :=
  forall f : FailureFamily,
    f = FailureFamily.silentRedescription \/
    f = FailureFamily.identityDrift \/
    f = FailureFamily.deferredValidation \/
    f = FailureFamily.postHocRehabilitation \/
    f = FailureFamily.scopeOrEnvelopeDrift

def GovernanceExhaustion : Prop :=
  GovernanceLociExhausted /\ FailureFamiliesExhausted

def LawfullyEquivalentAtGovernanceRoleLevel
    {Act : Type}
    (R G : GovernanceSystem Act) : Prop :=
  AASCClass R <-> AASCClass G

/--
Stronger downstream context tying the paper to the repo's existing
standing-emergence / no-repair / standing-conservation machinery.
-/
structure DerivedContext (α : Type) where
  B : InvariantBundle α
  S : System α
  rel : α -> α -> Prop
  Admitted : α -> Prop
  licensed_same_scope_continuation : Redescription α α -> Prop
  preserves_relevant_invariants : α -> Redescription α α -> Prop
  scope_preserving : (α -> α) -> Prop
  h_env_preserves :
    envelope_preserves_invariants B (standing_refinement_status S) scope_preserving
  h_rel_interface :
    same_target_rel_interface B rel
  h_adm :
    forall a : α, standing S a -> Admitted a
  h_pres :
    forall a : α,
      standing S a ->
      forall f : Redescription α α,
        licensed_same_scope_continuation f ->
        preserves_relevant_invariants a f
  h_internal :
    internally_fixed_auxiliary_datum rel (standing_refinement_status S)
  h_status_admitted_only :
    forall a : α,
      admitted_only S Admitted a ->
      standing_refinement_status S a = StandingRefinementLabel.admittedOnly
  h_status_standing :
    forall a : α,
      standing S a ->
      standing_refinement_status S a = StandingRefinementLabel.standingBearing
  h_substantive_if_admitted_only :
    forall a : α,
      admitted_only S Admitted a ->
      substantive_positive_refinement S Admitted (standing_refinement_status S) scope_preserving

theorem LegacyDerivedStandingEmergence
    {α : Type}
    (ctx : DerivedContext α) :
    forall a : α,
      standing ctx.S a <->
      reuse_stably_admissible
        ctx.Admitted
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  exact
    standing_emergence_theorem_paper
      ctx.B
      ctx.S
      ctx.rel
      ctx.Admitted
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      ctx.scope_preserving
      ctx.h_env_preserves
      ctx.h_rel_interface
      ctx.h_adm
      ctx.h_pres
      ctx.h_internal
      ctx.h_substantive_if_admitted_only

theorem PaperNoSameActRepairDerivedStatement
    {α : Type}
    (ctx : DerivedContext α)
    (T : Redescription α α)
    (a : α)
    (h_fail : Not (standing ctx.S a))
    (h_repair : standing ctx.S (T a) -> a = T a) :
    Not (standing ctx.S (T a)) := by
  exact
    MaleyLean.PaperNoSameActRepairStatement
      ctx.S
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      T
      a
      h_fail
      h_repair

theorem LegacyPaperStandingConservationDerivedStatement
    {α : Type}
    (ctx : DerivedContext α) :
    forall a : α,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a) := by
  exact
    MaleyLean.PaperStandingConservationStatement
      ctx.S
      ctx.Admitted
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      (fun a ha =>
        (LegacyDerivedStandingEmergence ctx a).mpr ha)

theorem LegacyDerivedStandingSelfEmergence
    {α : Type}
    (ctx : DerivedContext α) :
    forall a : α,
      standing ctx.S a <->
      reuse_stably_admissible
        (fun x => standing ctx.S x)
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  exact
    standing_emergence_theorem_paper
      ctx.B
      ctx.S
      ctx.rel
      (fun x => standing ctx.S x)
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      ctx.scope_preserving
      ctx.h_env_preserves
      ctx.h_rel_interface
      (fun a ha => ha)
      ctx.h_pres
      ctx.h_internal
      (fun a ha => False.elim (ha.2 ha.1))

theorem LegacyPaperNoSecondAdmissibilityInvariantDerivedStatement
    {α : Type}
    (ctx : DerivedContext α)
    (Q : α -> Prop)
    (h_gatework :
      forall a : α,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : α,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a) :
    forall a : α, Q a <-> standing ctx.S a := by
  exact
    MaleyLean.PaperNoPrimitiveCarriersStandingFormStatement
      ctx.S
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      Q
      (LegacyDerivedStandingSelfEmergence ctx)
      h_gatework
      h_ext

theorem LegacyPaperNoFourthAdmissibilityRoleDerivedStatement
    {α : Type}
    (ctx : DerivedContext α)
    (ρ : α -> ATSRole)
    (R : α -> Prop)
    (h_tensor_gatework :
      forall a : α,
        tensor_region ρ a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : α,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region ρ a)
    (hR_to_standing :
      forall a : α, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : α, standing ctx.S a -> R a) :
    lawfully_equivalent_interiors R (tensor_region ρ) := by
  have h_tensor :
      forall a : α, tensor_region ρ a <-> standing ctx.S a := by
    exact
      ATSTensorRegionCollapseStatement
        ctx.S
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        ρ
        (LegacyDerivedStandingSelfEmergence ctx)
        h_tensor_gatework
        h_tensor_ext
  exact
    ATSNoFourthStandingBearingRoleStatement
      ctx.S
      ρ
      R
      h_tensor
      hR_to_standing
      hStanding_to_R

theorem PaperInferentialLifeExhaustionDerivedStatement
    {A T G : Type}
    (acts : A)
    (trajs : T)
    (sameStandingClassification : G -> G -> Prop)
    (sameTrajectoryBehavior : G -> G -> Prop)
    (sameInferentialLife : G -> G -> Prop)
    (h_exhaust :
      forall g₁ g₂ : G,
        sameStandingClassification g₁ g₂ ->
        sameTrajectoryBehavior g₁ g₂ ->
        sameInferentialLife g₁ g₂) :
    forall g₁ g₂ : G,
      sameStandingClassification g₁ g₂ ->
      sameTrajectoryBehavior g₁ g₂ ->
      sameInferentialLife g₁ g₂ := by
  exact
    MaleyLean.PaperFixedDomainInferentialLifeExhaustionStatement
      (A := A)
      (T := T)
      (G := G)
      acts
      trajs
      sameStandingClassification
      sameTrajectoryBehavior
      sameInferentialLife
      h_exhaust

theorem PaperClosureRelevanceTransmissionDerivedStatement
    {A T Theta : Type}
    (D : InferentialLifeData A T Theta)
    (h_transmission :
      forall theta : Theta,
        D.changesInferentialLife theta ->
        D.changesStandingClassification theta \/
        D.changesTrajectoryStructure theta) :
    forall theta : Theta,
      D.changesInferentialLife theta ->
      D.changesStandingClassification theta \/
      D.changesTrajectoryStructure theta := by
  exact
    MaleyLean.PaperClosureRelevanceTransmissionStatement
      D
      h_transmission

theorem LegacyPaperDerivedCoreStatement
    {α A T Theta : Type}
    (ctx : DerivedContext α)
    (Q : α -> Prop)
    (ρ : α -> ATSRole)
    (R : α -> Prop)
    (D : InferentialLifeData A T Theta)
    (h_gatework :
      forall a : α,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : α,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a)
    (h_tensor_gatework :
      forall a : α,
        tensor_region ρ a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : α,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region ρ a)
    (hR_to_standing :
      forall a : α, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : α, standing ctx.S a -> R a)
    (h_transmission :
      forall theta : Theta,
        D.changesInferentialLife theta ->
        D.changesStandingClassification theta \/
        D.changesTrajectoryStructure theta) :
    (forall a : α, Q a <-> standing ctx.S a) /\
    lawfully_equivalent_interiors R (tensor_region ρ) /\
    (forall a : α,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)) /\
    (forall theta : Theta,
      D.changesInferentialLife theta ->
      D.changesStandingClassification theta \/
      D.changesTrajectoryStructure theta) := by
  refine And.intro ?_ ?_
  · exact
      LegacyPaperNoSecondAdmissibilityInvariantDerivedStatement
        ctx
        Q
        h_gatework
        h_ext
  refine And.intro ?_ ?_
  · exact
      LegacyPaperNoFourthAdmissibilityRoleDerivedStatement
        ctx
        ρ
        R
        h_tensor_gatework
        h_tensor_ext
        hR_to_standing
        hStanding_to_R
  refine And.intro ?_ ?_
  · exact LegacyPaperStandingConservationDerivedStatement ctx
  · exact
      PaperClosureRelevanceTransmissionDerivedStatement
        D
        h_transmission

/--
Manuscript-facing bridge from the stronger apex-closure package already
formalized elsewhere in the repo.

The extra four parameters supply the kernel/use fields that are not carried as
named fields by the apex package itself; the AASC-facing fields are imported
directly from `ApexStandaloneClosure`.
-/
def governanceSystemOfApex
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (governanceBearingNonDegenerateUse : Prop)
    (reference : Prop)
    (standingPersistence : Prop)
    (irreversibility : Prop) :
    GovernanceSystem Act where
  standing := fun a => standing S.base a
  licensedContinuation := S.admissibleContinuation
  governanceBearingNonDegenerateUse := governanceBearingNonDegenerateUse
  reference := reference
  standingPersistence := standingPersistence
  irreversibility := irreversibility
  priorGate := Papers.UnusSolusPossibilisEst.GatePredicateExists S
  failClosed := Papers.UnusSolusPossibilisEst.NoRepairsForEvaluatedActs S
  blocksSilentRedescription := Papers.UnusSolusPossibilisEst.NoIllicitScopeTransport S
  scopeIntegrity := Papers.UnusSolusPossibilisEst.TransferWithoutStanding S

theorem PaperBivalenceFromApexClosureDerivedStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    AASCClass (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  rcases h_apex with
    ⟨h_gate, _h_binary, _h_param, _h_unique_gate, h_no_repairs,
      _h_no_generators, _h_no_carriers, h_scope, h_transfer, _h_fixation,
      _h_discrete, _h_unique⟩
  exact And.intro h_gate (And.intro h_scope (And.intro h_transfer h_no_repairs))

theorem PaperNoKernelNeutralGovernanceDifferenceFromApexDerivedStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (_h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    ClosureRelevanceTransmission
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  intro a b h_diff
  exact h_diff

theorem PaperLocalClosureOfGovernanceFormFromApexDerivedStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    AASCClass (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    LawfullyEquivalentAtGovernanceRoleLevel
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev)
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  refine And.intro ?_ ?_
  · exact
      PaperBivalenceFromApexClosureDerivedStatement
        S
        h_apex
        h_use
        h_ref
        h_persist
        h_irrev
  · exact Iff.rfl

theorem PaperAASCRealizationFromApexClosureStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    h_ref ->
    h_persist ->
    h_irrev ->
    AASCClass (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    KernelRoles (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  intro hh_ref hh_persist hh_irrev
  refine And.intro ?_ ?_
  · exact
      PaperBivalenceFromApexClosureDerivedStatement
        S
        h_apex
        h_use
        h_ref
        h_persist
        h_irrev
  · exact And.intro hh_ref (And.intro hh_persist hh_irrev)

theorem PaperStrictBivalenceFromApexClosureStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    h_ref ->
    h_persist ->
    h_irrev ->
    AASCClass (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    LawfullyEquivalentAtGovernanceRoleLevel
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev)
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    KernelRoles (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  intro hh_ref hh_persist hh_irrev
  refine And.intro ?_ ?_
  · exact
      PaperBivalenceFromApexClosureDerivedStatement
        S
        h_apex
        h_use
        h_ref
        h_persist
        h_irrev
  refine And.intro Iff.rfl ?_
  exact And.intro hh_ref (And.intro hh_persist hh_irrev)

theorem PaperLocalClosureSufficiencyStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_local :
      StandingConservation R /\
      ClosureRelevanceTransmission R /\
      GovernanceExhaustion) :
    StandingConservation R /\
    ClosureRelevanceTransmission R /\
    GovernanceExhaustion := by
  exact h_local

theorem PaperNoSameActRepairStatement
    {Act : Type}
    (R : GovernanceSystem Act) :
    NoSameActRepair R := by
  intro a T h_not_standing h_same
  simpa [h_same] using h_not_standing

theorem PaperGateNecessityStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_gate :
      KernelRoles R ->
      R.governanceBearingNonDegenerateUse ->
      R.priorGate)
    (h_kernel : KernelRoles R)
    (h_use : R.governanceBearingNonDegenerateUse) :
    R.priorGate := by
  exact h_gate h_kernel h_use

theorem PaperFailClosedGovernanceStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_failClosed :
      KernelRoles R ->
      R.governanceBearingNonDegenerateUse ->
      R.failClosed)
    (h_kernel : KernelRoles R)
    (h_use : R.governanceBearingNonDegenerateUse) :
    R.failClosed := by
  exact h_failClosed h_kernel h_use

theorem PaperNoSecondAdmissibilityInvariantStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (I : Act -> Prop)
    (hI : NoSecondSameScopeAdmissibilityInvariant R I) :
    NoSecondSameScopeAdmissibilityInvariant R I := by
  exact hI

theorem PaperNoFourthAdmissibilityRoleStatement :
    SameScopeRoleExhaustion := by
  intro r
  cases r with
  | anchor =>
      exact Or.inl rfl
  | tensor =>
      exact Or.inr (Or.inl rfl)
  | skin =>
      exact Or.inr (Or.inr rfl)

theorem PaperStandingConservationStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_gate : R.priorGate)
    (h_failClosed : R.failClosed) :
    StandingConservation R := by
  exact
    And.intro
      (PaperNoSameActRepairStatement R)
      (And.intro h_gate h_failClosed)

theorem PaperInferentialLifeExhaustionStatement
    {Act : Type}
    (R : GovernanceSystem Act) :
    InferentialLifeExhausted R := by
  intro a b h_same
  exact h_same

theorem PaperClosureRelevanceTransmissionStatement
    {Act : Type}
    (R : GovernanceSystem Act) :
    ClosureRelevanceTransmission R := by
  intro a b h_diff
  exact h_diff

theorem PaperGovernanceExhaustionStatement :
    GovernanceExhaustion := by
  refine And.intro ?_ ?_
  · intro l
    cases l with
    | verdictStability =>
        exact Or.inl rfl
    | actIdentity =>
        exact Or.inr (Or.inl rfl)
    | evaluationOrder =>
        exact Or.inr (Or.inr (Or.inl rfl))
    | reversibility =>
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | scopeIntegrity =>
        exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · intro f
    cases f with
    | silentRedescription =>
        exact Or.inl rfl
    | identityDrift =>
        exact Or.inr (Or.inl rfl)
    | deferredValidation =>
        exact Or.inr (Or.inr (Or.inl rfl))
    | postHocRehabilitation =>
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | scopeOrEnvelopeDrift =>
        exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem PaperBivalenceOfNonDegenerateReasoningStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_gate : R.priorGate)
    (h_redescription : R.blocksSilentRedescription)
    (h_scope : R.scopeIntegrity)
    (h_failClosed : R.failClosed) :
    AASCClass R := by
  exact And.intro h_gate (And.intro h_redescription (And.intro h_scope h_failClosed))

theorem PaperAASCRealizationStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_realizes :
      AASCClass R ->
      KernelRoles R)
    (h_aasc : AASCClass R) :
    KernelRoles R := by
  exact h_realizes h_aasc

theorem PaperNoKernelNeutralGovernanceDifferenceStatement
    {Act : Type}
    (R : GovernanceSystem Act) :
    ClosureRelevanceTransmission R := by
  exact PaperClosureRelevanceTransmissionStatement R

theorem PaperLocalClosureOfGovernanceFormStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_bivalence :
      KernelRoles R ->
      R.governanceBearingNonDegenerateUse ->
      AASCClass R)
    (h_kernel : KernelRoles R)
    (h_use : R.governanceBearingNonDegenerateUse) :
    AASCClass R /\
    LawfullyEquivalentAtGovernanceRoleLevel R R := by
  refine And.intro (h_bivalence h_kernel h_use) ?_
  exact Iff.rfl

/--
Constructive version of the derived context.

This avoids the classical `standing_refinement_status` path by taking an
explicit refinement-status function together with a decidability instance for
`standing`.
-/
structure ConstructiveDerivedContext (alpha : Type) where
  B : InvariantBundle alpha
  S : System alpha
  rel : alpha -> alpha -> Prop
  Admitted : alpha -> Prop
  licensed_same_scope_continuation : Redescription alpha alpha -> Prop
  preserves_relevant_invariants : alpha -> Redescription alpha alpha -> Prop
  RefStatus : alpha -> StandingRefinementLabel
  scope_preserving : (alpha -> alpha) -> Prop
  standing_decidable : DecidablePred (fun a : alpha => standing S a)
  h_env_preserves :
    envelope_preserves_invariants B RefStatus scope_preserving
  h_rel_interface :
    same_target_rel_interface B rel
  h_adm :
    forall a : alpha, standing S a -> Admitted a
  h_pres :
    forall a : alpha,
      standing S a ->
      forall f : Redescription alpha alpha,
        licensed_same_scope_continuation f ->
        preserves_relevant_invariants a f
  h_internal :
    internally_fixed_auxiliary_datum rel RefStatus
  h_status_admitted_only :
    forall a : alpha,
      admitted_only S Admitted a ->
      RefStatus a = StandingRefinementLabel.admittedOnly
  h_status_standing :
    forall a : alpha,
      standing S a ->
      RefStatus a = StandingRefinementLabel.standingBearing
  h_substantive_if_admitted_only :
    forall a : alpha,
      admitted_only S Admitted a ->
      substantive_positive_refinement S Admitted RefStatus scope_preserving

theorem ConstructiveDerivedStandingEmergence
    {alpha : Type}
    (ctx : ConstructiveDerivedContext alpha) :
    forall a : alpha,
      standing ctx.S a <->
      reuse_stably_admissible
        ctx.Admitted
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  let _ := ctx.standing_decidable
  exact
    PaperStandingEmergenceStatementConstructive
      ctx.B
      ctx.S
      ctx.rel
      ctx.Admitted
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      ctx.RefStatus
      ctx.scope_preserving
      ctx.h_env_preserves
      ctx.h_rel_interface
      ctx.h_adm
      ctx.h_pres
      ctx.h_internal
      ctx.h_status_admitted_only
      ctx.h_status_standing
      ctx.h_substantive_if_admitted_only

theorem ConstructiveDerivedStandingSelfEmergence
    {alpha : Type}
    (ctx : ConstructiveDerivedContext alpha) :
    forall a : alpha,
      standing ctx.S a <->
      reuse_stably_admissible
        (fun x => standing ctx.S x)
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  let _ := ctx.standing_decidable
  exact
    PaperStandingEmergenceStatementConstructive
      ctx.B
      ctx.S
      ctx.rel
      (fun x => standing ctx.S x)
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      ctx.RefStatus
      ctx.scope_preserving
      ctx.h_env_preserves
      ctx.h_rel_interface
      (fun a ha => ha)
      ctx.h_pres
      ctx.h_internal
      (fun a ha => False.elim (ha.2 ha.1))
      ctx.h_status_standing
      (fun a ha => False.elim (ha.2 ha.1))

theorem PaperStandingConservationConstructiveDerivedStatement
    {alpha : Type}
    (ctx : ConstructiveDerivedContext alpha) :
    forall a : alpha,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a) := by
  exact
    MaleyLean.PaperStandingConservationStatement
      ctx.S
      ctx.Admitted
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      (fun a ha =>
        (ConstructiveDerivedStandingEmergence ctx a).mpr ha)

theorem PaperNoSecondAdmissibilityInvariantConstructiveDerivedStatement
    {alpha : Type}
    (ctx : ConstructiveDerivedContext alpha)
    (Q : alpha -> Prop)
    (h_gatework :
      forall a : alpha,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a) :
    forall a : alpha, Q a <-> standing ctx.S a := by
  exact
    MaleyLean.PaperNoPrimitiveCarriersStandingFormStatement
      ctx.S
      ctx.licensed_same_scope_continuation
      ctx.preserves_relevant_invariants
      Q
      (ConstructiveDerivedStandingSelfEmergence ctx)
      h_gatework
      h_ext

theorem PaperNoFourthAdmissibilityRoleConstructiveDerivedStatement
    {alpha : Type}
    (ctx : ConstructiveDerivedContext alpha)
    (rho : alpha -> ATSRole)
    (R : alpha -> Prop)
    (h_tensor_gatework :
      forall a : alpha,
        tensor_region rho a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region rho a)
    (hR_to_standing :
      forall a : alpha, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : alpha, standing ctx.S a -> R a) :
    lawfully_equivalent_interiors R (tensor_region rho) := by
  have h_tensor :
      forall a : alpha, tensor_region rho a <-> standing ctx.S a := by
    exact
      ATSTensorRegionCollapseStatement
        ctx.S
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        rho
        (ConstructiveDerivedStandingSelfEmergence ctx)
        h_tensor_gatework
        h_tensor_ext
  exact
    ATSNoFourthStandingBearingRoleStatement
      ctx.S
      rho
      R
      h_tensor
      hR_to_standing
      hStanding_to_R

theorem PaperConstructiveDerivedCoreStatement
    {alpha A T Theta : Type}
    (ctx : ConstructiveDerivedContext alpha)
    (Q : alpha -> Prop)
    (rho : alpha -> ATSRole)
    (R : alpha -> Prop)
    (D : InferentialLifeData A T Theta)
    (h_gatework :
      forall a : alpha,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a)
    (h_tensor_gatework :
      forall a : alpha,
        tensor_region rho a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region rho a)
    (hR_to_standing :
      forall a : alpha, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : alpha, standing ctx.S a -> R a)
    (h_transmission :
      forall theta : Theta,
        D.changesInferentialLife theta ->
        D.changesStandingClassification theta \/
        D.changesTrajectoryStructure theta) :
    (forall a : alpha, Q a <-> standing ctx.S a) /\
    lawfully_equivalent_interiors R (tensor_region rho) /\
    (forall a : alpha,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)) /\
    (forall theta : Theta,
      D.changesInferentialLife theta ->
      D.changesStandingClassification theta \/
      D.changesTrajectoryStructure theta) := by
  refine And.intro ?_ ?_
  · exact
      PaperNoSecondAdmissibilityInvariantConstructiveDerivedStatement
        ctx
        Q
        h_gatework
        h_ext
  refine And.intro ?_ ?_
  · exact
      PaperNoFourthAdmissibilityRoleConstructiveDerivedStatement
        ctx
        rho
        R
        h_tensor_gatework
        h_tensor_ext
        hR_to_standing
        hStanding_to_R
  refine And.intro ?_ ?_
  · exact PaperStandingConservationConstructiveDerivedStatement ctx
  · exact
      PaperClosureRelevanceTransmissionDerivedStatement
        D
        h_transmission

/-- Explicit registry of the superseded classical bridge theorem names. -/
def LegacyBridgeNames : List String :=
  [ "LegacyDerivedStandingEmergence"
  , "LegacyDerivedStandingSelfEmergence"
  , "LegacyPaperStandingConservationDerivedStatement"
  , "LegacyPaperNoSecondAdmissibilityInvariantDerivedStatement"
  , "LegacyPaperNoFourthAdmissibilityRoleDerivedStatement"
  , "LegacyPaperDerivedCoreStatement"
  , "derived_standing_emergence (compatibility wrapper)"
  , "derived_standing_self_emergence (compatibility wrapper)"
  , "PaperStandingConservationDerivedStatement (compatibility wrapper)"
  , "PaperNoSecondAdmissibilityInvariantDerivedStatement (compatibility wrapper)"
  , "PaperNoFourthAdmissibilityRoleDerivedStatement (compatibility wrapper)"
  , "PaperDerivedCoreStatement (compatibility wrapper)"
  ]

/-- Explicit registry of the current recommended axiom-free bridge theorem names. -/
def CurrentBridgeNames : List String :=
  [ "ConstructiveDerivedStandingEmergence"
  , "ConstructiveDerivedStandingSelfEmergence"
  , "PaperStandingConservationConstructiveDerivedStatement"
  , "PaperNoSecondAdmissibilityInvariantConstructiveDerivedStatement"
  , "PaperNoFourthAdmissibilityRoleConstructiveDerivedStatement"
  , "PaperConstructiveDerivedCoreStatement"
  , "PaperBivalenceFromApexClosureDerivedStatement"
  , "PaperAASCRealizationFromApexClosureStatement"
  , "PaperStrictBivalenceFromApexClosureStatement"
  , "Surface.ApexSummaryStatement"
  ]

/--
Legacy classical bridge declarations.

These remain only for compatibility with earlier work on this module.
They are not the current recommended route. Prefer the constructive
replacements below:

- `ConstructiveDerivedStandingEmergence`
- `ConstructiveDerivedStandingSelfEmergence`
- `PaperStandingConservationConstructiveDerivedStatement`
- `PaperNoSecondAdmissibilityInvariantConstructiveDerivedStatement`
- `PaperNoFourthAdmissibilityRoleConstructiveDerivedStatement`
- `PaperConstructiveDerivedCoreStatement`
-/
def LegacyClassicalBridgeNotice : String :=
  "Legacy classical bridge only: prefer the constructive derived bridge or the apex bridge."

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem derived_standing_emergence
    {alpha : Type}
    (ctx : DerivedContext alpha) :
    forall a : alpha,
      standing ctx.S a <->
      reuse_stably_admissible
        ctx.Admitted
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  exact LegacyDerivedStandingEmergence ctx

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem PaperStandingConservationDerivedStatement
    {alpha : Type}
    (ctx : DerivedContext alpha) :
    forall a : alpha,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a) := by
  exact LegacyPaperStandingConservationDerivedStatement ctx

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem derived_standing_self_emergence
    {alpha : Type}
    (ctx : DerivedContext alpha) :
    forall a : alpha,
      standing ctx.S a <->
      reuse_stably_admissible
        (fun x => standing ctx.S x)
        ctx.licensed_same_scope_continuation
        ctx.preserves_relevant_invariants
        a := by
  exact LegacyDerivedStandingSelfEmergence ctx

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem PaperNoSecondAdmissibilityInvariantDerivedStatement
    {alpha : Type}
    (ctx : DerivedContext alpha)
    (Q : alpha -> Prop)
    (h_gatework :
      forall a : alpha,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a) :
    forall a : alpha, Q a <-> standing ctx.S a := by
  exact
    LegacyPaperNoSecondAdmissibilityInvariantDerivedStatement
      ctx
      Q
      h_gatework
      h_ext

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem PaperNoFourthAdmissibilityRoleDerivedStatement
    {alpha : Type}
    (ctx : DerivedContext alpha)
    (rho : alpha -> ATSRole)
    (R : alpha -> Prop)
    (h_tensor_gatework :
      forall a : alpha,
        tensor_region rho a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region rho a)
    (hR_to_standing :
      forall a : alpha, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : alpha, standing ctx.S a -> R a) :
    lawfully_equivalent_interiors R (tensor_region rho) := by
  exact
    LegacyPaperNoFourthAdmissibilityRoleDerivedStatement
      ctx
      rho
      R
      h_tensor_gatework
      h_tensor_ext
      hR_to_standing
      hStanding_to_R

/-- Compatibility wrapper preserving the pre-cleanup theorem name. -/
theorem PaperDerivedCoreStatement
    {alpha A T Theta : Type}
    (ctx : DerivedContext alpha)
    (Q : alpha -> Prop)
    (rho : alpha -> ATSRole)
    (R : alpha -> Prop)
    (D : InferentialLifeData A T Theta)
    (h_gatework :
      forall a : alpha,
        Q a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        Q a)
    (h_tensor_gatework :
      forall a : alpha,
        tensor_region rho a ->
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)
    (h_tensor_ext :
      forall a : alpha,
        reuse_stably_admissible
          (fun x => standing ctx.S x)
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a ->
        tensor_region rho a)
    (hR_to_standing :
      forall a : alpha, R a -> standing ctx.S a)
    (hStanding_to_R :
      forall a : alpha, standing ctx.S a -> R a)
    (h_transmission :
      forall theta : Theta,
        D.changesInferentialLife theta ->
        D.changesStandingClassification theta \/
        D.changesTrajectoryStructure theta) :
    (forall a : alpha, Q a <-> standing ctx.S a) /\
    lawfully_equivalent_interiors R (tensor_region rho) /\
    (forall a : alpha,
      Not (standing ctx.S a) ->
      Not
        (reuse_stably_admissible
          ctx.Admitted
          ctx.licensed_same_scope_continuation
          ctx.preserves_relevant_invariants
          a)) /\
    (forall theta : Theta,
      D.changesInferentialLife theta ->
      D.changesStandingClassification theta \/
      D.changesTrajectoryStructure theta) := by
  exact
    LegacyPaperDerivedCoreStatement
      ctx
      Q
      rho
      R
      D
      h_gatework
      h_ext
      h_tensor_gatework
      h_tensor_ext
      hR_to_standing
      hStanding_to_R
      h_transmission

end BivalenceNonDegenerateReasoning
end Papers
end MaleyLean

