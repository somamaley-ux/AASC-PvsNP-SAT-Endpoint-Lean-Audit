import MaleyLean.Foundation
import MaleyLean.NoCarriers
import MaleyLean.StandingConservation
import MaleyLean.Bivalence
import MaleyLean.InteriorUniqueness
import MaleyLean.BivalenceUniqueness
import MaleyLean.UniquenessPaperStatements
import MaleyLean.GlobalMetricFixationPaperStatements
import MaleyLean.Papers.StandardModel.Structural.MetaClosureStatements
import MaleyLean.Papers.UnusSolusPossibilisEst.Verbatim.TheoremRegister

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst

/--
Manuscript-facing structural package for the main theorem spine of
"Unus Solus Possibilis Est".
-/
structure ApexClosureSystem (Act Domain : Type) where
  base : System Act
  typed : Domain -> Prop
  gate : Domain -> Act -> Prop
  standingDefined : Domain -> Prop
  dac : Domain -> Prop
  admissibleContinuation : Act -> Act -> Prop
  referenceFixed : Domain -> Prop
  theoryLevelConfirmation : Domain -> Prop
  gateDecidable : forall D a, Decidable (gate D a)
  Admitted : Act -> Prop
  licensed_same_scope_continuation : Redescription Act Act → Prop
  preserves_relevant_invariants : Act → Redescription Act Act → Prop
  gate_agrees_with_standing :
    ∀ D a, standingDefined D → (gate D a ↔ standing base a)

def StandingOne
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (_D : Domain)
    (a : Act) : Prop :=
  standing S.base a

def StandingZero
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (_D : Domain)
    (a : Act) : Prop :=
  failure_region S.base a

def GatePredicateExists
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D, S.typed D -> exists G : Act -> Prop, forall a, G a ↔ standing S.base a

def BinaryStanding
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D a, S.standingDefined D -> S.gate D a \/ Not (S.gate D a)

def NoAdmissibilityRelevantParameterization
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (Idx : Type) (classify : Idx -> Act -> Prop),
    S.typed D ->
    (forall i a, classify i a -> S.gate D a) ->
    forall i j a, classify i a -> classify j a

def UniqueGateClassification
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (G G' : Act -> Prop),
    S.typed D ->
    (forall a, G a ↔ standing S.base a) ->
    (forall a, G' a ↔ standing S.base a) ->
    forall a, G a <-> G' a

def NoRepairsForEvaluatedActs
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D a a',
    StandingZero S D a ->
    a' = a ->
    Not (StandingOne S D a')

def NoGenerators
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (T : Act -> Act) a,
    StandingZero S D a ->
    T a = a ->
    Not (StandingOne S D (T a))

def PrimitiveAuthorizer
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (_D : Domain)
  (Q : Act -> Prop) : Prop :=
  forall a,
    Q a ↔
    reuse_stably_admissible
      (fun x => standing S.base x)
      S.licensed_same_scope_continuation
      S.preserves_relevant_invariants
      a

def CarrierAttempt
    {Act Domain : Type}
    (_S : ApexClosureSystem Act Domain)
    (_D : Domain)
    (Q : Act -> Prop) : Prop :=
  exists a, Q a

def ProbabilisticCarrierAttempt
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop) : Prop :=
  CarrierAttempt S D Q

def ExplanatoryCarrierAttempt
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop) : Prop :=
  CarrierAttempt S D Q

def NoPrimitiveCarriers
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (Q : Act -> Prop),
    S.typed D ->
    CarrierAttempt S D Q ->
    PrimitiveAuthorizer S D Q ->
    (forall a,
      standing S.base a ↔
      reuse_stably_admissible
        (fun x => standing S.base x)
        S.licensed_same_scope_continuation
        S.preserves_relevant_invariants
        a) ->
    forall a, Q a ↔ standing S.base a

def ProbabilityNotPrimitive
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (Q : Act -> Prop),
    S.typed D ->
    ProbabilisticCarrierAttempt S D Q ->
    PrimitiveAuthorizer S D Q ->
    (forall a,
      standing S.base a ↔
      reuse_stably_admissible
        (fun x => standing S.base x)
        S.licensed_same_scope_continuation
        S.preserves_relevant_invariants
        a) ->
    forall a, Q a ↔ standing S.base a

def ExplanationNotPrimitive
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (Q : Act -> Prop),
    S.typed D ->
    ExplanatoryCarrierAttempt S D Q ->
    PrimitiveAuthorizer S D Q ->
    (forall a,
      standing S.base a ↔
      reuse_stably_admissible
        (fun x => standing S.base x)
        S.licensed_same_scope_continuation
        S.preserves_relevant_invariants
        a) ->
    forall a, Q a ↔ standing S.base a

def LegitimacyConservation
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  NoRepairsForEvaluatedActs S /\ NoGenerators S /\ NoPrimitiveCarriers S

def NoIllicitScopeTransport
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (S' : System Act)
    (T : Redescription Act Act),
    F.licensedFixation D T ->
    D' ≠ D ->
    ¬ F.independentlyAdmissible D' T ->
    (illicit_scope_transport F D D' T →
      silent_redescription_failure S.base S' T) ->
    ¬ redescription_legal S.base S' T

def TransferClaim
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D1 D2 : Domain)
    (a : Act) : Prop :=
  Not (D1 = D2) /\ standing S.base a

def TransferWithoutStanding
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (S' : System Act)
    (T : Redescription Act Act),
    F.licensedFixation D T ->
    D' ≠ D ->
    ¬ F.independentlyAdmissible D' T ->
    (illicit_scope_transport F D D' T →
      silent_redescription_failure S.base S' T) ->
    ∃ a, standing S.base a ∧ ¬ standing S' (T a)

def ReferenceFixationNecessary
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D, S.theoryLevelConfirmation D -> S.referenceFixed D

structure AdmissibleInterior
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain) where
  carrier : Act -> Prop
  gateClosed : forall a, carrier a -> S.gate D a
  closedUnderContinuation :
    forall a a', carrier a -> S.admissibleContinuation a a' -> carrier a'
  maximal :
    forall J : Act -> Prop,
      (forall a, J a -> S.gate D a) ->
      (forall a a', J a -> S.admissibleContinuation a a' -> J a') ->
      (forall a, carrier a -> J a) ->
      forall a, J a -> carrier a

def InteriorMatchesStanding
    {Act Domain : Type}
    {S : ApexClosureSystem Act Domain}
    {D : Domain}
    (I : AdmissibleInterior S D) : Prop :=
  forall a, I.carrier a <-> standing S.base a

def DistinctInteriors
    {Act Domain : Type}
    {S : ApexClosureSystem Act Domain}
    {D : Domain}
    (I1 I2 : AdmissibleInterior S D) : Prop :=
  exists a, (I1.carrier a /\ Not (I2.carrier a)) \/ (I2.carrier a /\ Not (I1.carrier a))

def DiscreteMultiplicityElimination
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D (I1 I2 : AdmissibleInterior S D),
    S.typed D ->
    Not (DistinctInteriors I1 I2)

def UniqueAdmissibleInterior
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  forall D,
    S.typed D ->
    exists I : AdmissibleInterior S D,
      forall J : AdmissibleInterior S D, forall a, J.carrier a <-> I.carrier a

def ApexStandaloneClosure
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  GatePredicateExists S /\
  BinaryStanding S /\
  NoAdmissibilityRelevantParameterization S /\
  UniqueGateClassification S /\
  NoRepairsForEvaluatedActs S /\
  NoGenerators S /\
  NoPrimitiveCarriers S /\
  NoIllicitScopeTransport S /\
  TransferWithoutStanding S /\
  ReferenceFixationNecessary S /\
  DiscreteMultiplicityElimination S /\
  UniqueAdmissibleInterior S

theorem PaperGateExistenceIsForcedByIrreversibilityAndIntelligibilityStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_gate : GatePredicateExists S) :
    GatePredicateExists S := by
  exact h_gate

theorem PaperBinaryStandingWhenDefinedStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) :
    BinaryStanding S := by
  intro D a h_defined
  match S.gateDecidable D a with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

theorem PaperNoAdmissibilityRelevantParameterizationStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_param : NoAdmissibilityRelevantParameterization S) :
    NoAdmissibilityRelevantParameterization S := by
  exact h_param

theorem PaperUniquenessOfAdmissibilityClassificationStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (_h_unique_gate : UniqueGateClassification S) :
    UniqueGateClassification S := by
  intro D G G' hD hG hG' a
  constructor
  · intro hGa
    exact (hG' a).mpr ((hG a).mp hGa)
  · intro hG'a
    exact (hG a).mpr ((hG' a).mp hG'a)

theorem PaperNoRepairsForAnEvaluatedActStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_no_repairs : NoRepairsForEvaluatedActs S) :
    NoRepairsForEvaluatedActs S := by
  exact h_no_repairs

theorem PaperNoRepairsForAnEvaluatedActFromStandardModelStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (licensed_same_scope_continuation : Redescription Act Act → Prop)
    (preserves_relevant_invariants : Act → Redescription Act Act → Prop) :
    NoRepairsForEvaluatedActs S := by
  intro D a a' hZero hEq
  subst a'
  have hFail : Not (standing S.base a) :=
    (failure_region_is_negated_standing S.base a).mp hZero
  simpa using
    PaperStandardModelNoStandingRepairStatement
      S.base
      licensed_same_scope_continuation
      preserves_relevant_invariants
      id
      a
      hFail
      (by intro _; rfl)

theorem PaperNoGeneratorsStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_no_generators : NoGenerators S) :
    NoGenerators S := by
  exact h_no_generators

theorem PaperNoGeneratorsFromStandardModelStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    :
    NoGenerators S := by
  intro D T a hZero hEq hStanding
  have hFail : Not (standing S.base a) :=
    (failure_region_is_negated_standing S.base a).mp hZero
  exact
    PaperStandardModelNoCanonicalRepresentativeStatement
      S.base
      T
      a
      hFail
      hStanding
      hEq

theorem PaperAnyPrimitiveAuthorizerIsAGatePredicateStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop)
    (h_auth : PrimitiveAuthorizer S D Q) :
    forall a,
      Q a ↔
      reuse_stably_admissible
        (fun x => standing S.base x)
        S.licensed_same_scope_continuation
        S.preserves_relevant_invariants
        a := by
  exact h_auth

theorem PaperNoCarriersNumericOrStructuralStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop)
    (_hD : S.typed D)
    (_hCarrier : CarrierAttempt S D Q)
    (hAuth : PrimitiveAuthorizer S D Q)
    (hEmergence :
      forall a,
        standing S.base a ↔
        reuse_stably_admissible
          (fun x => standing S.base x)
          S.licensed_same_scope_continuation
          S.preserves_relevant_invariants
          a) :
    forall a, Q a ↔ standing S.base a := by
  exact
    no_primitive_carriers_standing_form
      S.base
      S.licensed_same_scope_continuation
      S.preserves_relevant_invariants
      Q
      hEmergence
      (fun a hQa => (hAuth a).mp hQa)
      (fun a hRa => (hAuth a).mpr hRa)

theorem PaperStandingCannotBeRecoveredByReuseStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (hEmergence :
      forall a,
        reuse_stably_admissible
          S.Admitted
          S.licensed_same_scope_continuation
          S.preserves_relevant_invariants
          a ->
        standing S.base a) :
    forall a,
      Not (standing S.base a) ->
      Not
        (reuse_stably_admissible
          S.Admitted
          S.licensed_same_scope_continuation
          S.preserves_relevant_invariants
          a) := by
  exact
    standing_conservation
      S.base
      S.Admitted
      S.licensed_same_scope_continuation
      S.preserves_relevant_invariants
      hEmergence

theorem PaperProbabilityAndTypicalityAreNotPrimitiveStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop)
    (hD : S.typed D)
    (hCarrier : ProbabilisticCarrierAttempt S D Q)
    (hAuth : PrimitiveAuthorizer S D Q)
    (hEmergence :
      forall a,
        standing S.base a ↔
        reuse_stably_admissible
          (fun x => standing S.base x)
          S.licensed_same_scope_continuation
          S.preserves_relevant_invariants
          a) :
    forall a, Q a ↔ standing S.base a := by
  exact
    PaperNoCarriersNumericOrStructuralStatement
      S D Q hD hCarrier hAuth hEmergence

theorem PaperExplanationCannotBePrimitiveStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (Q : Act -> Prop)
    (hD : S.typed D)
    (hCarrier : ExplanatoryCarrierAttempt S D Q)
    (hAuth : PrimitiveAuthorizer S D Q)
    (hEmergence :
      forall a,
        standing S.base a ↔
        reuse_stably_admissible
          (fun x => standing S.base x)
          S.licensed_same_scope_continuation
          S.preserves_relevant_invariants
          a) :
    forall a, Q a ↔ standing S.base a := by
  exact
    PaperNoCarriersNumericOrStructuralStatement
      S D Q hD hCarrier hAuth hEmergence

theorem PaperLegitimacyConservationClosedRegimeStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_cons : LegitimacyConservation S) :
    LegitimacyConservation S := by
  exact h_cons

theorem PaperLegitimacyConservationFromStandardModelStatements
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (licensed_same_scope_continuation : Redescription Act Act → Prop)
    (preserves_relevant_invariants : Act → Redescription Act Act → Prop)
    (h_carriers : NoPrimitiveCarriers S) :
    LegitimacyConservation S := by
  refine And.intro ?_ ?_
  · exact
      PaperNoRepairsForAnEvaluatedActFromStandardModelStatement
        S
        licensed_same_scope_continuation
        preserves_relevant_invariants
  · exact And.intro (PaperNoGeneratorsFromStandardModelStatement S) h_carriers

theorem PaperNoIllicitScopeTransportStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_scope : NoIllicitScopeTransport S) :
    NoIllicitScopeTransport S := by
  exact h_scope

theorem PaperNoIllicitScopeTransportFromFixationPacketStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) :
    NoIllicitScopeTransport S := by
  intro F D D' S' T hLicense hScopeChange hNoFresh hFailure
  exact
    illicit_scope_transport_blocks_legality
      F
      D
      D'
      S.base
      S'
      T
      (fixation_extension_is_illicit_without_fresh_admissibility
        F
        D
        D'
        T
        (And.intro hLicense hScopeChange)
        hNoFresh)
      hFailure

theorem PaperFixationExtensionIsIllicitScopeTransportStatement
    {Act Domain : Type}
    (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (T : Redescription Act Act)
    (h_license : F.licensedFixation D T)
    (h_scope_change : D' ≠ D)
    (h_no_fresh : ¬ F.independentlyAdmissible D' T) :
    illicit_scope_transport F D D' T := by
  exact
    fixation_extension_is_illicit_without_fresh_admissibility
      F
      D
      D'
      T
      (And.intro h_license h_scope_change)
      h_no_fresh

theorem PaperIllicitScopeTransportBlocksLegalityStatement
    {Act Domain : Type}
    (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (S₁ S₂ : System Act)
    (T : Redescription Act Act)
    (h_illicit : illicit_scope_transport F D D' T)
    (h_failure :
      illicit_scope_transport F D D' T →
      silent_redescription_failure S₁ S₂ T) :
    ¬ redescription_legal S₁ S₂ T := by
  exact
    illicit_scope_transport_blocks_legality
      F
      D
      D'
      S₁
      S₂
      T
      h_illicit
      h_failure

theorem PaperIllicitScopeTransportForcesStandingFailureStatement
    {Act Domain : Type}
    (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (S₁ S₂ : System Act)
    (T : Redescription Act Act)
    (h_illicit : illicit_scope_transport F D D' T)
    (h_failure :
      illicit_scope_transport F D D' T →
      silent_redescription_failure S₁ S₂ T) :
    ∃ a, standing S₁ a ∧ ¬ standing S₂ (T a) := by
  exact
    illicit_scope_transport_implies_terminal_standing_failure
      F
      D
      D'
      S₁
      S₂
      T
      h_illicit
      h_failure

theorem PaperTransferWithoutStandingStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_transfer : TransferWithoutStanding S) :
    TransferWithoutStanding S := by
  exact h_transfer

theorem PaperTransferWithoutStandingFromFixationPacketStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) :
    TransferWithoutStanding S := by
  intro F D D' S' T hLicense hScopeChange hNoFresh hFailure
  exact
    illicit_scope_transport_implies_terminal_standing_failure
      F
      D
      D'
      S.base
      S'
      T
      (fixation_extension_is_illicit_without_fresh_admissibility
        F
        D
        D'
        T
        (And.intro hLicense hScopeChange)
        hNoFresh)
      hFailure

theorem PaperTransferWithoutFreshAdmissibilityStatement
    {Act Domain : Type}
    (F : ScopeRelativeFixation Domain Act)
    (D D' : Domain)
    (S₁ S₂ : System Act)
    (T : Redescription Act Act)
    (h_license : F.licensedFixation D T)
    (h_scope_change : D' ≠ D)
    (h_no_fresh : ¬ F.independentlyAdmissible D' T)
    (h_failure :
      illicit_scope_transport F D D' T →
      silent_redescription_failure S₁ S₂ T) :
    ¬ redescription_legal S₁ S₂ T ∧
    ∃ a, standing S₁ a ∧ ¬ standing S₂ (T a) := by
  have hIllicit :
      illicit_scope_transport F D D' T :=
    PaperFixationExtensionIsIllicitScopeTransportStatement
      F
      D
      D'
      T
      h_license
      h_scope_change
      h_no_fresh
  refine And.intro ?_ ?_
  · exact
      PaperIllicitScopeTransportBlocksLegalityStatement
        F
        D
        D'
        S₁
        S₂
        T
        hIllicit
        h_failure
  · exact
      PaperIllicitScopeTransportForcesStandingFailureStatement
        F
        D
        D'
        S₁
        S₂
        T
        hIllicit
        h_failure

theorem PaperReferenceFixationIsNecessaryForTheoryLevelConfirmationStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_fixation : ReferenceFixationNecessary S) :
    ReferenceFixationNecessary S := by
  exact h_fixation

theorem PaperDiscreteMultiplicityEliminationGateFormStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_discrete : DiscreteMultiplicityElimination S) :
    DiscreteMultiplicityElimination S := by
  exact h_discrete

theorem PaperDiscreteMultiplicityEliminationFromSharedInteriorUniquenessStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (I1 I2 : AdmissibleInterior S D)
    (h1 : InteriorMatchesStanding I1)
    (h2 : InteriorMatchesStanding I2) :
    Not (DistinctInteriors I1 I2) := by
  intro hDistinct
  have hEq :
      forall a, I1.carrier a <-> I2.carrier a :=
    PaperNoPluralAdmissibleCoresStatement
      S.base
      I1.carrier
      I2.carrier
      (fun a hI1 => (h1 a).mp hI1)
      (fun a hI2 => (h2 a).mp hI2)
      (fun a hStanding => (h1 a).mpr hStanding)
      (fun a hStanding => (h2 a).mpr hStanding)
  rcases hDistinct with ⟨a, hSep⟩
  cases hSep with
  | inl hLeft =>
      exact hLeft.2 ((hEq a).mp hLeft.1)
  | inr hRight =>
      exact hRight.2 ((hEq a).mpr hRight.1)

theorem PaperUniquenessOfTheAdmissibleInteriorStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_unique : UniqueAdmissibleInterior S) :
    UniqueAdmissibleInterior S := by
  exact h_unique

theorem PaperUniquenessOfTheAdmissibleInteriorFromSharedCoreStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (I J : AdmissibleInterior S D)
    (hI : InteriorMatchesStanding I)
    (hJ : InteriorMatchesStanding J) :
    forall a, J.carrier a <-> I.carrier a := by
  exact
    PaperNoPluralAdmissibleCoresStatement
      S.base
      J.carrier
      I.carrier
      (fun a hJa => (hJ a).mp hJa)
      (fun a hIa => (hI a).mp hIa)
      (fun a hStanding => (hJ a).mpr hStanding)
      (fun a hStanding => (hI a).mpr hStanding)

theorem PaperApexStandaloneClosureStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_gate : GatePredicateExists S)
    (h_binary : BinaryStanding S)
    (h_param : NoAdmissibilityRelevantParameterization S)
    (h_unique_gate : UniqueGateClassification S)
    (h_no_repairs : NoRepairsForEvaluatedActs S)
    (h_no_generators : NoGenerators S)
    (h_no_carriers : NoPrimitiveCarriers S)
    (h_scope : NoIllicitScopeTransport S)
    (h_transfer : TransferWithoutStanding S)
    (h_fixation : ReferenceFixationNecessary S)
    (h_discrete : DiscreteMultiplicityElimination S)
    (h_unique : UniqueAdmissibleInterior S) :
    ApexStandaloneClosure S := by
  refine And.intro h_gate ?_
  refine And.intro h_binary ?_
  refine And.intro h_param ?_
  refine And.intro h_unique_gate ?_
  refine And.intro h_no_repairs ?_
  refine And.intro h_no_generators ?_
  refine And.intro h_no_carriers ?_
  refine And.intro h_scope ?_
  refine And.intro h_transfer ?_
  refine And.intro h_fixation ?_
  exact And.intro h_discrete h_unique

end UnusSolusPossibilisEst
end Papers
end MaleyLean
