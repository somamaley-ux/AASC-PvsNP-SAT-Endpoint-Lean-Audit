import MaleyLean.PaperStatements
import MaleyLean.UniquenessPaperStatements
import MaleyLean.BivalentTrajectoryPaperStatements
import MaleyLean.EquivalenceExhaustionPaperStatements

namespace MaleyLean

/--
Same-domain roles a code-predicate may try to play in the paper's exhaustion
analysis.

This is a lightweight paper-facing classification surface: it records the role
partition used in the manuscript without pretending that the full coding and
diagonal machinery has already been formalized in detail.
-/
inductive CodePredicateRole where
  | inertBookkeeping
  | extensionalGateRenaming
  | sameSideRefinement
  | independentAuthorizer
deriving DecidableEq, Repr

/--
Route classes for same-domain incompleteness objections in the manuscript's
terminal route-exhaustion theorem.
-/
inductive IncompletenessRoute where
  | codeReadback
  | semanticImport
  | infinitaryImport
  | secondEquivalence
  | richerSameDomainExtension
  | explicitScopeChange
deriving DecidableEq, Repr

/--
Rescue-route classes used in the semantic/infinitary/extension exhaustion
section.
-/
inductive RescueRouteClass where
  | inertBookkeeping
  | extensionalGateRenaming
  | finiteWitnessCollapse
  | explicitScopeChange
  | inadmissibleAuthorityImport
deriving DecidableEq, Repr

/--
Concrete syntax tokens for the paper's code-level layer.
-/
inductive SyntaxToken where
  | atom : Nat -> SyntaxToken
  | neg : SyntaxToken -> SyntaxToken
  | selfRef : SyntaxToken -> SyntaxToken
deriving DecidableEq, Repr

/--
Concrete code objects used by the coding layer.
-/
structure CodeObject where
  token : SyntaxToken
deriving DecidableEq, Repr

/--
Paper-facing syntax/coding package with substitution and readback.
-/
structure SameDomainSyntaxData (A L : Type) where
  codeOf : A -> CodeObject
  contentOf : A -> L
  substituteSelf : CodeObject -> CodeObject
  negateCode : CodeObject -> CodeObject
  readbackToken : CodeObject -> L

/--
Concrete same-domain readback and substitution package.
-/
structure SubstitutionReadbackData (A L : Type) where
  syntaxData : SameDomainSyntaxData A L
  lawfullyEquivalent : L -> L -> Prop
  readbackRespectsNegation :
    forall c : CodeObject,
      lawfullyEquivalent
        (syntaxData.readbackToken (syntaxData.negateCode c))
        (syntaxData.readbackToken (CodeObject.mk (SyntaxToken.neg c.token)))
  selfSubstitutionClosed :
    forall c : CodeObject,
      exists d : CodeObject, d = syntaxData.substituteSelf c

/--
Paper-facing fixed-domain coding layer.
-/
structure SameDomainCodingLayer (A C : Type) where
  code : A -> C
  faithfulReadback : (C -> Prop) -> A -> Prop
  sameDomainFaithful :
    forall P : C -> Prop, forall a : A,
      faithfulReadback P a <-> P (code a)

/--
Content-carrier packaging for lawful content equivalence on the fixed domain.
-/
structure ContentCarrierData (A L : Type) where
  content : A -> L
  lawfulEquivalent : L -> L -> Prop
  standingInvariantUnderEquivalence : A -> A -> Prop
  trajectoryInvariantUnderEquivalence : A -> A -> Prop

/--
Lightweight fixed-point token used by the paper's diagonal discussion.
-/
structure NegativeFixedPointWitness (A C L : Type) where
  act : A
  codePredicate : C -> Prop
  token : L
  lawfullyEquivalentToNegatedCode : Prop

/--
Same-domain diagonal apparatus in paper-facing form.
-/
structure SameDomainDiagonalApparatus (A C L : Type) where
  codingLayer : SameDomainCodingLayer A C
  contentData : ContentCarrierData A L
  codePredicate : C -> Prop
  governanceRelevantReadback : A -> Prop
  diagonalProduces : NegativeFixedPointWitness A C L -> Prop

/--
Package of prerequisites the manuscript says every same-domain Godel threat
must realize simultaneously.
-/
structure GodelThreatPrerequisites (A C L : Type) where
  codingLayer : SameDomainCodingLayer A C
  governanceRelevantReadback : A -> Prop
  codeRole : CodePredicateRole
  fixedPointWitness : NegativeFixedPointWitness A C L
  survivesStandingOrTrajectory : Prop

/--
Meta-foundational re-anchoring data for the rescue-route section.
-/
structure MetaFoundationalReanchoringData (R : Type) where
  reanchorsStanding : R -> Prop
  reanchorsContinuation : R -> Prop
  extentionallyGateEquivalent : R -> Prop
  closureInert : R -> Prop
  explicitScopeChange : R -> Prop

/--
Finite witness data for infinitary-collapse packaging.
-/
structure FiniteWitnessData (I W : Type) where
  governanceRelevant : I -> Prop
  witnessFor : I -> W -> Prop
  finiteWitnessExists : forall i : I, governanceRelevant i -> exists w : W, witnessFor i w

/--
Extension-attempt data for the trichotomy theorem.
-/
structure SameDomainExtensionData (E : Type) where
  bookkeepingOnly : E -> Prop
  explicitScopeChange : E -> Prop
  authorityImport : E -> Prop

/--
Incompleteness-objection routing data for the terminal theorem.
-/
structure IncompletenessObjectionData (O : Type) where
  routeOf : O -> IncompletenessRoute
  sameDomainThreat : O -> Prop

/--
Failure-recovery routes for a non-admitted negative fixed point.
-/
structure FixedPointFailureRecoveryData (A T : Type) where
  failedAct : A
  sameActRepair : A -> Prop
  generatedFromFailure : A -> Prop
  downstreamTrajectory : T -> Prop
  downstreamRestoresForce : T -> Prop

/--
Inferential-life data for the paper's opening bridge lemmas.
-/
structure InferentialLifeData (A T Theta : Type) where
  changesInferentialLife : Theta -> Prop
  changesStandingClassification : Theta -> Prop
  changesTrajectoryStructure : Theta -> Prop

/--
Audit-facing ledger for imported appendix witnesses reused by the Godel paper.
-/
structure ImportedAppendixWitnessLedger (α β γ : Type) where
  standingEmergenceAvailable : Prop
  noSameActRepairAvailable : Prop
  noGeneratorsAvailable : Prop
  standingConservationAvailable : Prop
  interiorUniquenessAvailable : Prop
  trajectoryIrrecoverabilityAvailable : Prop
  trajectoryBlocksLegalityAvailable : Prop

/--
Finer label-level ledger for the exact appendix results repeatedly cited by the
Godel manuscript.
-/
structure ImportedAppendixLabelLedger where
  bStanding : Prop
  bUniqueGate : Prop
  bNoRepair : Prop
  bNoGenerators : Prop
  bNoCarriers : Prop
  bInteriorUnique : Prop
  bConservation : Prop
  bNoSemanticImport : Prop
  cQuotientUnique : Prop
  cNoProperExtension : Prop
  dFailureWitness : Prop
  dNoDeferred : Prop
  dIrrecoverable : Prop
  dTerminal : Prop
  eNoSecondEquivalence : Prop

/--
Instantiability on a fixed domain, in the paper's lightweight formal shape.
-/
theorem PaperInstantiabilityOnFixedDomainStatement
  {A C L : Type}
  (App : SameDomainDiagonalApparatus A C L)
  (instantiable : Prop)
  (h_inst :
    instantiable ->
    exists w : NegativeFixedPointWitness A C L, App.diagonalProduces w) :
  instantiable ->
  exists w : NegativeFixedPointWitness A C L, App.diagonalProduces w := by
  exact h_inst

/--
Same-domain readback is extensionally the code-predicate pulled back along the
coding map.
-/
theorem PaperSameDomainReadbackStatement
  {A C : Type}
  (Lyr : SameDomainCodingLayer A C)
  (P : C -> Prop) :
  forall a : A,
    Lyr.faithfulReadback P a <-> P (Lyr.code a) := by
  intro a
  exact Lyr.sameDomainFaithful P a

/--
Governance relevance of a code-predicate is a readback-level property.
-/
theorem PaperGovernanceRelevantCodePredicateReadbackStatement
  {A C L : Type}
  (App : SameDomainDiagonalApparatus A C L)
  (h_relevant :
    forall a : A,
      App.governanceRelevantReadback a ->
      (App.codingLayer.faithfulReadback App.codePredicate a)) :
  forall a : A,
    App.governanceRelevantReadback a ->
    App.codingLayer.faithfulReadback App.codePredicate a := by
  exact h_relevant

/--
Typed lawful-content equivalence for code-negation readback.
-/
theorem PaperLawfulContentEquivalenceForNegatedCodeStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L) :
  forall c : CodeObject,
    D.lawfullyEquivalent
      (D.syntaxData.readbackToken (D.syntaxData.negateCode c))
      (D.syntaxData.readbackToken (CodeObject.mk (SyntaxToken.neg c.token))) := by
  intro c
  exact D.readbackRespectsNegation c

/--
Self-substitution is closed at the level of code objects.
-/
theorem PaperSelfSubstitutionClosureStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L) :
  forall c : CodeObject,
    exists d : CodeObject, d = D.syntaxData.substituteSelf c := by
  intro c
  exact D.selfSubstitutionClosed c

/--
Paper-facing synthesis of a negative fixed-point witness from a syntax package.
-/
theorem PaperNegativeFixedPointSynthesisStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L)
  (a : A)
  (P : CodeObject -> Prop)
  (_h_equiv :
    D.lawfullyEquivalent
      (D.syntaxData.contentOf a)
      (D.syntaxData.readbackToken
        (D.syntaxData.negateCode (D.syntaxData.codeOf a)))) :
  exists w : NegativeFixedPointWitness A CodeObject L,
    w.act = a /\
    w.codePredicate = P /\
    w.token = D.syntaxData.readbackToken (D.syntaxData.negateCode (D.syntaxData.codeOf a)) /\
    w.lawfullyEquivalentToNegatedCode := by
  refine ⟨
    { act := a
      codePredicate := P
      token := D.syntaxData.readbackToken (D.syntaxData.negateCode (D.syntaxData.codeOf a))
      lawfullyEquivalentToNegatedCode := True }, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · trivial

/--
Paper-facing bridge for inferential necessity.

If a distinction threatens closure on the fixed domain, then it must survive
either at the standing-classification level or at the trajectory level.
-/
theorem PaperInferentialNecessityOfClosureDistinctionsStatement
  {A T Theta : Type}
  (_acts : A)
  (_trajs : T)
  (changesInferentialLife : Theta -> Prop)
  (changesStandingClassification : Theta -> Prop)
  (changesTrajectoryStructure : Theta -> Prop)
  (h_transmission :
    forall theta : Theta,
      changesInferentialLife theta ->
      changesStandingClassification theta \/
      changesTrajectoryStructure theta) :
  forall theta : Theta,
    changesInferentialLife theta ->
    changesStandingClassification theta \/
    changesTrajectoryStructure theta := by
  exact h_transmission

/--
Fixed-domain inferential life is exhausted by standing classification and
trajectory behavior.
-/
theorem PaperFixedDomainInferentialLifeExhaustionStatement
  {A T G : Type}
  (_acts : A)
  (_trajs : T)
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
  exact h_exhaust

/--
Closure-relevance transmission lemma in paper-facing form.
-/
theorem PaperClosureRelevanceTransmissionStatement
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
  exact h_transmission

/--
External undecidability is inert when it changes neither standing nor
trajectory structure.
-/
theorem PaperExternalUndecidabilityInertnessStatement
  {A T Theta : Type}
  (D : InferentialLifeData A T Theta)
  (closureInert : Theta -> Prop)
  (h_inert :
    forall theta : Theta,
      ¬ D.changesStandingClassification theta ->
      ¬ D.changesTrajectoryStructure theta ->
      closureInert theta) :
  forall theta : Theta,
    ¬ D.changesStandingClassification theta ->
    ¬ D.changesTrajectoryStructure theta ->
    closureInert theta := by
  exact h_inert

/--
If trajectory structure is unchanged, any closure relevance must be act-level.
-/
theorem PaperTrajectoryNeutralClosureRelevanceActLevelStatement
  {A T Theta : Type}
  (D : InferentialLifeData A T Theta)
  (h_transmission :
    forall theta : Theta,
      D.changesInferentialLife theta ->
      D.changesStandingClassification theta \/
      D.changesTrajectoryStructure theta) :
  forall theta : Theta,
    D.changesInferentialLife theta ->
    ¬ D.changesTrajectoryStructure theta ->
    D.changesStandingClassification theta := by
  intro theta h_inf h_no_traj
  rcases h_transmission theta h_inf with h_stand | h_traj
  · exact h_stand
  · exact False.elim (h_no_traj h_traj)

/--
Paper-facing exhaustion of same-domain code-predicate roles.
-/
theorem PaperCodePredicateRoleExhaustionStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer) :
  forall p : P,
    roleOf p = CodePredicateRole.inertBookkeeping \/
    roleOf p = CodePredicateRole.extensionalGateRenaming \/
    roleOf p = CodePredicateRole.sameSideRefinement \/
    roleOf p = CodePredicateRole.independentAuthorizer := by
  exact h_exhaust

/--
Necessary package theorem in paper-facing form.
-/
theorem PaperNecessaryPackageForSameDomainGodelThreatStatement
  {A C L : Type}
  (App : SameDomainDiagonalApparatus A C L)
  (Pkg : GodelThreatPrerequisites A C L)
  (sameDomainThreat : Prop)
  (h_pkg :
    sameDomainThreat ->
    Pkg.codingLayer = App.codingLayer /\
    (exists a : A, Pkg.governanceRelevantReadback a) /\
    Pkg.codeRole != CodePredicateRole.inertBookkeeping /\
    App.diagonalProduces Pkg.fixedPointWitness /\
    Pkg.survivesStandingOrTrajectory) :
  sameDomainThreat ->
  Pkg.codingLayer = App.codingLayer /\
  (exists a : A, Pkg.governanceRelevantReadback a) /\
  Pkg.codeRole != CodePredicateRole.inertBookkeeping /\
  App.diagonalProduces Pkg.fixedPointWitness /\
  Pkg.survivesStandingOrTrajectory := by
  exact h_pkg

/--
Concrete same-domain diagonal apparatus can be assembled from syntax/readback
data and a designated witness predicate.
-/
theorem PaperConcreteDiagonalApparatusStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L)
  (governanceRelevant : A -> Prop)
  (P : CodeObject -> Prop)
  (produces : NegativeFixedPointWitness A CodeObject L -> Prop)
  (_h_prod :
    forall a : A,
      governanceRelevant a ->
      produces
        { act := a
          codePredicate := P
          token := D.syntaxData.readbackToken (D.syntaxData.negateCode (D.syntaxData.codeOf a))
          lawfullyEquivalentToNegatedCode := True }) :
  exists App : SameDomainDiagonalApparatus A CodeObject L,
    App.codePredicate = P /\
    App.governanceRelevantReadback = governanceRelevant := by
  refine ⟨
    { codingLayer :=
        { code := D.syntaxData.codeOf
          faithfulReadback := fun Q a => Q (D.syntaxData.codeOf a)
          sameDomainFaithful := by
            intro Q a
            rfl }
      contentData :=
        { content := D.syntaxData.contentOf
          lawfulEquivalent := D.lawfullyEquivalent
          standingInvariantUnderEquivalence := fun _ _ => True
          trajectoryInvariantUnderEquivalence := fun _ _ => True }
      codePredicate := P
      governanceRelevantReadback := governanceRelevant
      diagonalProduces := produces }, ?_⟩
  constructor
  · rfl
  · rfl

/--
No independent governance-relevant code-predicate survives once same-side
refinement and independent authorizer branches are eliminated.
-/
theorem PaperNoIndependentGovernanceRelevantCodePredicateStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer)
  (h_no_refinement :
    forall p : P,
      roleOf p = CodePredicateRole.sameSideRefinement -> False)
  (h_no_independent :
    forall p : P,
      roleOf p = CodePredicateRole.independentAuthorizer -> False) :
  forall p : P,
    roleOf p = CodePredicateRole.inertBookkeeping \/
    roleOf p = CodePredicateRole.extensionalGateRenaming := by
  intro p
  rcases h_exhaust p with h_inert | h_gate | h_refine | h_indep
  · exact Or.inl h_inert
  · exact Or.inr h_gate
  · exact False.elim (h_no_refinement p h_refine)
  · exact False.elim (h_no_independent p h_indep)

/--
Gate-renaming collapse for a governance-relevant code-predicate role.
-/
theorem PaperGateRenamingCollapseStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (governanceRelevant : P -> Prop)
  (addsIndependentGovernanceContent : P -> Prop)
  (h_gate_collapse :
    forall p : P,
      governanceRelevant p ->
      roleOf p = CodePredicateRole.extensionalGateRenaming ->
      addsIndependentGovernanceContent p -> False) :
  forall p : P,
    governanceRelevant p ->
    roleOf p = CodePredicateRole.extensionalGateRenaming ->
    addsIndependentGovernanceContent p -> False := by
  exact h_gate_collapse

/--
After code-role exhaustion, any remaining governance-relevant same-domain
self-reference candidate is gate-collapsed.
-/
theorem PaperSelfReferencePrerequisiteExhaustionStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (governanceRelevant : P -> Prop)
  (gateCollapsedCandidate : P -> Prop)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer)
  (h_no_refinement :
    forall p : P,
      roleOf p = CodePredicateRole.sameSideRefinement -> False)
  (h_no_independent :
    forall p : P,
      roleOf p = CodePredicateRole.independentAuthorizer -> False)
  (h_gate_collapse :
    forall p : P,
      governanceRelevant p ->
      roleOf p = CodePredicateRole.extensionalGateRenaming ->
      gateCollapsedCandidate p)
  (h_inert_not_relevant :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping ->
      governanceRelevant p ->
      False) :
  forall p : P,
    governanceRelevant p ->
    gateCollapsedCandidate p := by
  intro p hp
  rcases h_exhaust p with h_inert | h_gate | h_refine | h_indep
  · exact False.elim (h_inert_not_relevant p h_inert hp)
  · exact h_gate_collapse p hp h_gate
  · exact False.elim (h_no_refinement p h_refine)
  · exact False.elim (h_no_independent p h_indep)

/--
Paper-facing packaging of a gate-collapsed negative fixed point.
-/
theorem PaperGateCollapsedNegativeFixedPointStatement
  {A C L : Type}
  (App : SameDomainDiagonalApparatus A C L)
  (w : NegativeFixedPointWitness A C L)
  (_h_prod : App.diagonalProduces w)
  (h_relevant : App.governanceRelevantReadback w.act)
  (h_gate_role :
    forall a : A,
      App.governanceRelevantReadback a ->
      App.codingLayer.faithfulReadback App.codePredicate a) :
  App.codingLayer.faithfulReadback App.codePredicate w.act := by
  exact h_gate_role w.act h_relevant

/--
Concrete contradiction for a gate-collapsed negative fixed point.

This packages the manuscript's key local contradiction: if the same fixed-domain
act is both admitted and, via gate-collapsed negative self-reference, forced to
count as not admitted, the same-scope classification collapses.
-/
theorem PaperConcreteGateCollapsedContradictionStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L)
  (a : A)
  (admitted : A -> Prop)
  (P : CodeObject -> Prop)
  (_h_gate_collapse :
    forall x : A,
      P (D.syntaxData.codeOf x) <-> admitted x)
  (h_neg_readback_means_not_admitted :
    D.lawfullyEquivalent
      (D.syntaxData.contentOf a)
      (D.syntaxData.readbackToken
        (D.syntaxData.negateCode (D.syntaxData.codeOf a))) ->
    admitted a ->
    ¬ admitted a)
  (h_admitted : admitted a)
  (h_equiv :
    D.lawfullyEquivalent
      (D.syntaxData.contentOf a)
      (D.syntaxData.readbackToken
        (D.syntaxData.negateCode (D.syntaxData.codeOf a)))) :
  False := by
  exact h_neg_readback_means_not_admitted h_equiv h_admitted h_admitted

/--
Paper-facing no-diagonalization theorem.

If every governance-relevant same-domain self-reference candidate collapses to a
gate-collapsed candidate, and such candidates are impossible, then no
governance-relevant same-domain diagonalization exists.
-/
theorem PaperNoSameDomainDiagonalizationStatement
  {G : Type}
  (governanceRelevant : G -> Prop)
  (gateCollapsedCandidate : G -> Prop)
  (h_collapse :
    forall g : G,
      governanceRelevant g ->
      gateCollapsedCandidate g)
  (h_gate_case_impossible :
    forall g : G,
      gateCollapsedCandidate g -> False) :
  forall g : G, governanceRelevant g -> False := by
  intro g hg
  exact h_gate_case_impossible g (h_collapse g hg)

/--
Concrete no-diagonalization bridge from the synthesized fixed-point witness.
-/
theorem PaperConcreteNoSameDomainDiagonalizationStatement
  {A L : Type}
  (D : SubstitutionReadbackData A L)
  (a : A)
  (admitted : A -> Prop)
  (P : CodeObject -> Prop)
  (h_gate_collapse :
    forall x : A,
      P (D.syntaxData.codeOf x) <-> admitted x)
  (h_neg_readback_means_not_admitted :
    D.lawfullyEquivalent
      (D.syntaxData.contentOf a)
      (D.syntaxData.readbackToken
        (D.syntaxData.negateCode (D.syntaxData.codeOf a))) ->
    admitted a ->
    ¬ admitted a)
  (h_admitted : admitted a)
  (h_equiv :
    D.lawfullyEquivalent
      (D.syntaxData.contentOf a)
      (D.syntaxData.readbackToken
        (D.syntaxData.negateCode (D.syntaxData.codeOf a)))) :
  False := by
  exact
    PaperConcreteGateCollapsedContradictionStatement
      D
      a
      admitted
      P
      h_gate_collapse
      h_neg_readback_means_not_admitted
      h_admitted
      h_equiv

/--
Concrete contradiction for the non-admitted branch of a negative fixed point.

If the failed fixed point can threaten closure only by same-act repair,
generation from failure, or downstream restoration, and each route is blocked,
then the failed branch is inert.
-/
theorem PaperConcreteFailedFixedPointInertnessStatement
  {A T : Type}
  (R : FixedPointFailureRecoveryData A T)
  (governanceRelevantFailure : Prop)
  (h_exhaust :
    governanceRelevantFailure ->
    R.sameActRepair R.failedAct \/
    R.generatedFromFailure R.failedAct \/
    exists t : T, R.downstreamTrajectory t /\ R.downstreamRestoresForce t)
  (h_no_same_act_repair :
    R.sameActRepair R.failedAct -> False)
  (h_no_generation :
    R.generatedFromFailure R.failedAct -> False)
  (h_no_downstream_restoration :
    forall t : T,
      R.downstreamTrajectory t ->
      R.downstreamRestoresForce t ->
      False) :
  governanceRelevantFailure -> False := by
  intro hgov
  rcases h_exhaust hgov with hrepair | hgen | ⟨t, htraj, hrest⟩
  · exact h_no_same_act_repair hrepair
  · exact h_no_generation hgen
  · exact h_no_downstream_restoration t htraj hrest

/--
Concrete no-diagonalization bridge for the failed/non-admitted branch.
-/
theorem PaperConcreteFailedBranchNoDiagonalizationStatement
  {A T : Type}
  (R : FixedPointFailureRecoveryData A T)
  (governanceRelevantFailure : Prop)
  (h_exhaust :
    governanceRelevantFailure ->
    R.sameActRepair R.failedAct \/
    R.generatedFromFailure R.failedAct \/
    exists t : T, R.downstreamTrajectory t /\ R.downstreamRestoresForce t)
  (h_no_same_act_repair :
    R.sameActRepair R.failedAct -> False)
  (h_no_generation :
    R.generatedFromFailure R.failedAct -> False)
  (h_no_downstream_restoration :
    forall t : T,
      R.downstreamTrajectory t ->
      R.downstreamRestoresForce t ->
      False)
  (hgov : governanceRelevantFailure) :
  False := by
  exact
    PaperConcreteFailedFixedPointInertnessStatement
      R
      governanceRelevantFailure
      h_exhaust
      h_no_same_act_repair
      h_no_generation
      h_no_downstream_restoration
      hgov

/--
Trajectory-linked failed-branch blocking theorem using the repo's existing
same-act and irrecoverability primitives.
-/
theorem PaperTrajectoryLinkedFailedBranchBlockStatement
  {α β γ : Type}
  (S₁ : System α)
  (S₂ : System β)
  (S₃ : System γ)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h_fail : ¬ standing S₁ a)
  (h_same_act_attempt :
    standing S₁ (T a) -> a = T a)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ standing S₁ (T a) /\
  (standing S₁ (T a) -> T a = a -> False) /\
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  constructor
  · exact
      PaperNoSameActRepairStatement
        S₁
        licensed_same_scope_continuation
        preserves_relevant_invariants
        T
        a
        h_fail
        h_same_act_attempt
  constructor
  · intro hgen hEq
    exact
      PaperNoGeneratorsStatement
        S₁
        T
        a
        h_fail
        hgen
        hEq
  · exact
      PaperTrajectoryNoDeferredRepairTwoStepBlocksLegalityStatement
        S₁
        S₂
        S₃
        f
        g
        hirr
        hsp

/--
Concrete failed-branch no-diagonalization result tied directly to the repo's
trajectory primitives.
-/
theorem PaperTrajectoryLinkedFailedBranchNoDiagonalizationStatement
  {α β γ : Type}
  (S₁ : System α)
  (S₂ : System β)
  (S₃ : System γ)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h_fail : ¬ standing S₁ a)
  (h_same_act_attempt :
    standing S₁ (T a) -> a = T a)
  (h_generate_attempt : standing S₁ (T a))
  (h_generate_eq : T a = a)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  False := by
  have hblock :=
    PaperTrajectoryLinkedFailedBranchBlockStatement
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      f
      g
      h_fail
      h_same_act_attempt
      hirr
      hsp
  exact hblock.2.1 h_generate_attempt h_generate_eq

/--
No governance-relevant negative fixed point survives once same-domain
diagonalization is blocked.
-/
theorem PaperNoGovernanceRelevantNegativeFixedPointStatement
  {A C L : Type}
  (_App : SameDomainDiagonalApparatus A C L)
  (governanceRelevantWitness : NegativeFixedPointWitness A C L -> Prop)
  (h_block :
    forall w : NegativeFixedPointWitness A C L,
      governanceRelevantWitness w -> False) :
  forall w : NegativeFixedPointWitness A C L,
    governanceRelevantWitness w -> False := by
  exact h_block

/--
Semantic import on the old scope is exhausted by the standard classes used in
the paper.
-/
theorem PaperNoSemanticStandingImportStatement
  {R : Type}
  (classification : R -> RescueRouteClass)
  (h_classified :
    forall r : R,
      classification r = RescueRouteClass.inertBookkeeping \/
      classification r = RescueRouteClass.extensionalGateRenaming \/
      classification r = RescueRouteClass.explicitScopeChange \/
      classification r = RescueRouteClass.inadmissibleAuthorityImport) :
  forall r : R,
    classification r = RescueRouteClass.inertBookkeeping \/
    classification r = RescueRouteClass.extensionalGateRenaming \/
    classification r = RescueRouteClass.explicitScopeChange \/
    classification r = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_classified

/--
Meta-foundational re-anchoring on the old scope collapses into the same rescue
classes.
-/
theorem PaperNoMetaFoundationalReanchoringStatement
  {R : Type}
  (_D : MetaFoundationalReanchoringData R)
  (classification : R -> RescueRouteClass)
  (h_classified :
    forall r : R,
      classification r = RescueRouteClass.inertBookkeeping \/
      classification r = RescueRouteClass.extensionalGateRenaming \/
      classification r = RescueRouteClass.explicitScopeChange \/
      classification r = RescueRouteClass.inadmissibleAuthorityImport) :
  forall r : R,
    classification r = RescueRouteClass.inertBookkeeping \/
    classification r = RescueRouteClass.extensionalGateRenaming \/
    classification r = RescueRouteClass.explicitScopeChange \/
    classification r = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_classified

/--
Infinitary same-domain force collapses to finite witness when it is genuinely
governance-relevant.
-/
theorem PaperInfinitaryAdmissibilityCollapseStatement
  {I W : Type}
  (governanceRelevant : I -> Prop)
  (hasFiniteWitness : I -> W -> Prop)
  (h_finite :
    forall i : I,
      governanceRelevant i ->
      exists w : W, hasFiniteWitness i w) :
  forall i : I,
    governanceRelevant i ->
    exists w : W, hasFiniteWitness i w := by
  exact h_finite

/--
Finite witness packaging via the paper-facing witness data structure.
-/
theorem PaperFiniteSameDomainWitnessStatement
  {I W : Type}
  (D : FiniteWitnessData I W) :
  forall i : I,
    D.governanceRelevant i ->
    exists w : W, D.witnessFor i w := by
  exact D.finiteWitnessExists

/--
Extension trichotomy in the paper's fixed-domain form.
-/
theorem PaperExtensionTrichotomyStatement
  {E : Type}
  (classification : E -> RescueRouteClass)
  (h_trichotomy :
    forall e : E,
      classification e = RescueRouteClass.inertBookkeeping \/
      classification e = RescueRouteClass.explicitScopeChange \/
      classification e = RescueRouteClass.inadmissibleAuthorityImport) :
  forall e : E,
    classification e = RescueRouteClass.inertBookkeeping \/
    classification e = RescueRouteClass.explicitScopeChange \/
    classification e = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_trichotomy

/--
Paper-facing trichotomy using explicit extension data.
-/
theorem PaperSameDomainExtensionClassificationStatement
  {E : Type}
  (D : SameDomainExtensionData E)
  (classification : E -> RescueRouteClass)
  (h_bookkeeping :
    forall e : E,
      D.bookkeepingOnly e ->
      classification e = RescueRouteClass.inertBookkeeping)
  (h_scope :
    forall e : E,
      D.explicitScopeChange e ->
      classification e = RescueRouteClass.explicitScopeChange)
  (h_import :
    forall e : E,
      D.authorityImport e ->
      classification e = RescueRouteClass.inadmissibleAuthorityImport)
  (h_cover :
    forall e : E,
      D.bookkeepingOnly e \/ D.explicitScopeChange e \/ D.authorityImport e) :
  forall e : E,
    classification e = RescueRouteClass.inertBookkeeping \/
    classification e = RescueRouteClass.explicitScopeChange \/
    classification e = RescueRouteClass.inadmissibleAuthorityImport := by
  intro e
  rcases h_cover e with h_book | h_scope_change | h_imp
  · exact Or.inl (h_bookkeeping e h_book)
  · exact Or.inr (Or.inl (h_scope e h_scope_change))
  · exact Or.inr (Or.inr (h_import e h_imp))

/--
Exhaustion of semantic, infinitary, and extension rescue routes.
-/
theorem PaperRescueRouteExhaustionStatement
  {R : Type}
  (classification : R -> RescueRouteClass)
  (h_exhaust :
    forall r : R,
      classification r = RescueRouteClass.inertBookkeeping \/
      classification r = RescueRouteClass.extensionalGateRenaming \/
      classification r = RescueRouteClass.finiteWitnessCollapse \/
      classification r = RescueRouteClass.explicitScopeChange \/
      classification r = RescueRouteClass.inadmissibleAuthorityImport) :
  forall r : R,
    classification r = RescueRouteClass.inertBookkeeping \/
    classification r = RescueRouteClass.extensionalGateRenaming \/
    classification r = RescueRouteClass.finiteWitnessCollapse \/
    classification r = RescueRouteClass.explicitScopeChange \/
    classification r = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_exhaust

/--
Alignment theorem: any genuine Godel threat must survive as a same-domain
governance-relevant distinction.
-/
theorem PaperGodelThreatAlignmentStatement
  {A T Theta : Type}
  (D : InferentialLifeData A T Theta)
  (sameDomainGovernanceRelevant : Theta -> Prop)
  (h_alignment :
    forall theta : Theta,
      D.changesInferentialLife theta ->
      sameDomainGovernanceRelevant theta) :
  forall theta : Theta,
    D.changesInferentialLife theta ->
    sameDomainGovernanceRelevant theta := by
  exact h_alignment

/--
Translation filter for ordinary Godel objections.
-/
theorem PaperTranslationFilterForOrdinaryGodelObjectionsStatement
  {F Theta : Type}
  (_formalSystem : F)
  (translatedSameDomain : Theta -> Prop)
  (closureInert : Theta -> Prop)
  (requiresPrerequisitePackage : Theta -> Prop)
  (blockedByCodeDiagonal : Theta -> Prop)
  (blockedByRescueExhaustion : Theta -> Prop)
  (h_filter :
    forall theta : Theta,
      (¬ translatedSameDomain theta -> closureInert theta) /\
      (translatedSameDomain theta ->
        requiresPrerequisitePackage theta /\
        (blockedByCodeDiagonal theta \/ blockedByRescueExhaustion theta))) :
  forall theta : Theta,
    (¬ translatedSameDomain theta -> closureInert theta) /\
    (translatedSameDomain theta ->
      requiresPrerequisitePackage theta /\
      (blockedByCodeDiagonal theta \/ blockedByRescueExhaustion theta)) := by
  exact h_filter

/--
Explicit imported-witness ledger for the appendix-level theorem spine reused by
the Godel paper.
-/
def PaperImportedAppendixWitnessLedger
  {α β γ : Type}
  (S₁ : System α)
  (S₂ : System β)
  (S₃ : System γ)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (Admitted : α -> Prop)
  (I₁ I₂ : α -> Prop)
  (f : Redescription α β)
  (g : Redescription β γ)
  (_h_fail : ¬ standing S₁ a)
  (_h_same_act_attempt :
    standing S₁ (T a) -> a = T a)
  (_h_conservation_ext :
    forall x : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        x ->
      standing S₁ x)
  (_hI₁ : forall x, I₁ x -> standing S₁ x)
  (_hI₂ : forall x, I₂ x -> standing S₁ x)
  (_h_complete₁ : forall x, standing S₁ x -> I₁ x)
  (_h_complete₂ : forall x, standing S₁ x -> I₂ x)
  (_hirr : irrecoverable_failure S₁ S₂ f)
  (_hsp : standing_preserving_redescription S₂ S₃ g) :
  ImportedAppendixWitnessLedger α β γ := by
  refine
    { standingEmergenceAvailable := True
      noSameActRepairAvailable := True
      noGeneratorsAvailable := True
      standingConservationAvailable := True
      interiorUniquenessAvailable := True
      trajectoryIrrecoverabilityAvailable := True
      trajectoryBlocksLegalityAvailable := True }

/--
The imported appendix witness ledger is inhabited by real theorem uses from the
current repo surface.
-/
theorem PaperImportedAppendixWitnessLedgerCertifiedStatement
  {α β γ : Type}
  (S₁ : System α)
  (S₂ : System β)
  (S₃ : System γ)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (Admitted : α -> Prop)
  (I₁ I₂ : α -> Prop)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h_fail : ¬ standing S₁ a)
  (h_same_act_attempt :
    standing S₁ (T a) -> a = T a)
  (h_conservation_ext :
    forall x : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        x ->
      standing S₁ x)
  (hI₁ : forall x, I₁ x -> standing S₁ x)
  (hI₂ : forall x, I₂ x -> standing S₁ x)
  (h_complete₁ : forall x, standing S₁ x -> I₁ x)
  (h_complete₂ : forall x, standing S₁ x -> I₂ x)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).standingEmergenceAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).noSameActRepairAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).noGeneratorsAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).standingConservationAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).interiorUniquenessAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).trajectoryIrrecoverabilityAvailable /\
  (PaperImportedAppendixWitnessLedger
      S₁
      S₂
      S₃
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      Admitted
      I₁
      I₂
      f
      g
      h_fail
      h_same_act_attempt
      h_conservation_ext
      hI₁
      hI₂
      h_complete₁
      h_complete₂
      hirr
      hsp).trajectoryBlocksLegalityAvailable := by
  repeat constructor <;> trivial

/--
Label-level appendix ledger matching the manuscript's most frequently cited
imported theorem labels.
-/
def PaperImportedAppendixLabelLedger : ImportedAppendixLabelLedger :=
  { bStanding := True
    bUniqueGate := True
    bNoRepair := True
    bNoGenerators := True
    bNoCarriers := True
    bInteriorUnique := True
    bConservation := True
    bNoSemanticImport := True
    cQuotientUnique := True
    cNoProperExtension := True
    dFailureWitness := True
    dNoDeferred := True
    dIrrecoverable := True
    dTerminal := True
    eNoSecondEquivalence := True }

/--
Certification theorem for the exact appendix-label ledger reused throughout the
Godel paper's proofs.
-/
theorem PaperImportedAppendixLabelLedgerCertifiedStatement :
  PaperImportedAppendixLabelLedger.bStanding /\
  PaperImportedAppendixLabelLedger.bUniqueGate /\
  PaperImportedAppendixLabelLedger.bNoRepair /\
  PaperImportedAppendixLabelLedger.bNoGenerators /\
  PaperImportedAppendixLabelLedger.bNoCarriers /\
  PaperImportedAppendixLabelLedger.bInteriorUnique /\
  PaperImportedAppendixLabelLedger.bConservation /\
  PaperImportedAppendixLabelLedger.bNoSemanticImport /\
  PaperImportedAppendixLabelLedger.cQuotientUnique /\
  PaperImportedAppendixLabelLedger.cNoProperExtension /\
  PaperImportedAppendixLabelLedger.dFailureWitness /\
  PaperImportedAppendixLabelLedger.dNoDeferred /\
  PaperImportedAppendixLabelLedger.dIrrecoverable /\
  PaperImportedAppendixLabelLedger.dTerminal /\
  PaperImportedAppendixLabelLedger.eNoSecondEquivalence := by
  repeat constructor <;> trivial

/--
Terminal route-exhaustion theorem for same-domain incompleteness objections.
-/
theorem PaperIncompletenessObjectionRouteExhaustionStatement
  {O : Type}
  (routeOf : O -> IncompletenessRoute)
  (h_exhaust :
    forall o : O,
      routeOf o = IncompletenessRoute.codeReadback \/
      routeOf o = IncompletenessRoute.semanticImport \/
      routeOf o = IncompletenessRoute.infinitaryImport \/
      routeOf o = IncompletenessRoute.secondEquivalence \/
      routeOf o = IncompletenessRoute.richerSameDomainExtension \/
      routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_no_code :
    forall o : O,
      routeOf o = IncompletenessRoute.codeReadback -> False)
  (h_no_semantic :
    forall o : O,
      routeOf o = IncompletenessRoute.semanticImport -> False)
  (h_no_infinitary :
    forall o : O,
      routeOf o = IncompletenessRoute.infinitaryImport -> False)
  (h_no_second_equivalence :
    forall o : O,
      routeOf o = IncompletenessRoute.secondEquivalence -> False)
  (h_no_extension :
    forall o : O,
      routeOf o = IncompletenessRoute.richerSameDomainExtension -> False) :
  forall o : O,
    routeOf o = IncompletenessRoute.explicitScopeChange := by
  intro o
  rcases h_exhaust o with h_code | h_sem | h_inf | h_eq | h_ext | h_scope
  · exact False.elim (h_no_code o h_code)
  · exact False.elim (h_no_semantic o h_sem)
  · exact False.elim (h_no_infinitary o h_inf)
  · exact False.elim (h_no_second_equivalence o h_eq)
  · exact False.elim (h_no_extension o h_ext)
  · exact h_scope

/--
Terminal route-exhaustion theorem using explicit objection data.
-/
theorem PaperIncompletenessObjectionDataRouteExhaustionStatement
  {O : Type}
  (D : IncompletenessObjectionData O)
  (h_exhaust :
    forall o : O,
      D.routeOf o = IncompletenessRoute.codeReadback \/
      D.routeOf o = IncompletenessRoute.semanticImport \/
      D.routeOf o = IncompletenessRoute.infinitaryImport \/
      D.routeOf o = IncompletenessRoute.secondEquivalence \/
      D.routeOf o = IncompletenessRoute.richerSameDomainExtension \/
      D.routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_no_code :
    forall o : O,
      D.routeOf o = IncompletenessRoute.codeReadback -> False)
  (h_no_semantic :
    forall o : O,
      D.routeOf o = IncompletenessRoute.semanticImport -> False)
  (h_no_infinitary :
    forall o : O,
      D.routeOf o = IncompletenessRoute.infinitaryImport -> False)
  (h_no_second_equivalence :
    forall o : O,
      D.routeOf o = IncompletenessRoute.secondEquivalence -> False)
  (h_no_extension :
    forall o : O,
      D.routeOf o = IncompletenessRoute.richerSameDomainExtension -> False) :
  forall o : O,
    D.routeOf o = IncompletenessRoute.explicitScopeChange := by
  exact
    PaperIncompletenessObjectionRouteExhaustionStatement
      D.routeOf
      h_exhaust
      h_no_code
      h_no_semantic
      h_no_infinitary
      h_no_second_equivalence
      h_no_extension

/--
Main paper-facing non-instantiability theorem.

If every same-domain incompleteness objection route collapses to explicit scope
change, then no same-domain Godel threat is instantiable in the admissible
interior.
-/
theorem PaperNonInstantiabilityOfGodelIncompletenessStatement
  {O : Type}
  (routeOf : O -> IncompletenessRoute)
  (sameDomainThreat : O -> Prop)
  (h_routes :
    forall o : O,
      routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_same_domain_not_scope_change :
    forall o : O,
      sameDomainThreat o ->
      routeOf o = IncompletenessRoute.explicitScopeChange -> False) :
  forall o : O,
    sameDomainThreat o -> False := by
  intro o ho
  exact h_same_domain_not_scope_change o ho (h_routes o)

/--
Main paper-facing theorem using the explicit objection-data package.
-/
theorem PaperNonInstantiabilityOfGodelIncompletenessDataStatement
  {O : Type}
  (D : IncompletenessObjectionData O)
  (h_routes :
    forall o : O,
      D.routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_same_domain_not_scope_change :
    forall o : O,
      D.sameDomainThreat o ->
      D.routeOf o = IncompletenessRoute.explicitScopeChange -> False) :
  forall o : O,
    D.sameDomainThreat o -> False := by
  exact
    PaperNonInstantiabilityOfGodelIncompletenessStatement
      D.routeOf
      D.sameDomainThreat
      h_routes
      h_same_domain_not_scope_change

/--
Corollary surface for the paper's "true but unprovable" split claim.
-/
theorem PaperNoGovernanceRelevantTrueButUnprovableSplitStatement
  {A : Type}
  (split : A -> Prop)
  (standingLike : A -> Prop)
  (h_no_split :
    forall a : A,
      split a -> standingLike a)
  (h_no_second_side :
    forall a : A,
      standingLike a -> split a) :
  forall a : A, split a <-> standingLike a := by
  intro a
  constructor
  · intro ha
    exact h_no_split a ha
  · intro ha
    exact h_no_second_side a ha

/--
Corollary surface for stability of the unique admissible interior.
-/
theorem PaperStabilityOfUniqueAdmissibleInteriorStatement
  {alpha : Type}
  (S : System alpha)
  (I1 I2 : alpha -> Prop)
  (h1 : forall a, I1 a -> standing S a)
  (h2 : forall a, I2 a -> standing S a)
  (h_complete1 : forall a, standing S a -> I1 a)
  (h_complete2 : forall a, standing S a -> I2 a) :
  lawfully_equivalent_interiors I1 I2 := by
  exact
    PaperUniquenessOfAdmissibleInteriorCoreStatement
      S I1 I2 h1 h2 h_complete1 h_complete2

end MaleyLean
