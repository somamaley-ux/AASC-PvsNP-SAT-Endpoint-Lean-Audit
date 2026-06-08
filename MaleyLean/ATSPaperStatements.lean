import MaleyLean.PaperStatements

namespace MaleyLean

/--
The three ATS roles as used in the role-decomposition paper.

This is intentionally lightweight: the ATS manuscript presents the role
decomposition as a corollary-level classification layer over the already-fixed
standing/admissibility surface, not as a new foundational level.
-/
inductive ATSRole where
  | anchor
  | tensor
  | skin
deriving DecidableEq, Repr

/--
The tensor-bearing region induced by an ATS role assignment.
-/
def tensor_region
  {α : Type}
  (ρ : α → ATSRole) : α → Prop :=
  fun a => ρ a = ATSRole.tensor

def anchor_region
  {α : Type}
  (ρ : α → ATSRole) : α → Prop :=
  fun a => ρ a = ATSRole.anchor

def skin_region
  {α : Type}
  (ρ : α → ATSRole) : α → Prop :=
  fun a => ρ a = ATSRole.skin

/--
ATS Definition 8, in lightweight fixed-carrier form.

The current Lean layer tracks only the minimal fixed-domain content needed by
the paper's imported-dependency posture: a role classifier over one carrier,
with the tensor region tied to the standing-bearing region.
-/
def admissibility_preserving_role_classification
  {α : Type}
  (S : System α)
  (ρ : α → ATSRole) : Prop :=
  ∀ a : α, tensor_region ρ a ↔ standing S a

/--
ATS Definition 9, specialized to the fixed three-role vocabulary.

Since ATS roles are already named canonically, role isomorphism reduces here to
agreement of the induced anchor/tensor/skin partition on the fixed carrier.
-/
def ats_role_isomorphic
  {α : Type}
  (ρ₁ ρ₂ : α → ATSRole) : Prop :=
  (∀ a : α, anchor_region ρ₁ a ↔ anchor_region ρ₂ a) ∧
  (∀ a : α, tensor_region ρ₁ a ↔ tensor_region ρ₂ a) ∧
  (∀ a : α, skin_region ρ₁ a ↔ skin_region ρ₂ a)

/--
ATS tensor-role collapse.

If the tensor-designated region does no more and no less than track the
standing-preserving reuse-stable region, then it collapses extensionally to
standing. This is the direct ATS-facing specialization of the existing
no-primitive-carriers standing form.
-/
theorem ATSTensorRegionCollapseStatement
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (ρ : α → ATSRole)
  (h_emergence :
    ∀ a : α,
      standing S a ↔
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_tensor_gatework :
    ∀ a : α,
      tensor_region ρ a →
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_tensor_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      tensor_region ρ a) :
  ∀ a : α, tensor_region ρ a ↔ standing S a := by
  exact
    PaperNoPrimitiveCarriersStandingFormStatement
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      (tensor_region ρ)
      h_emergence
      h_tensor_gatework
      h_tensor_ext

/--
ATS imported uniqueness dependency, packaged in tensor-role language.

This matches the paper's explicit dependency posture: the tensor-bearing region
is fixed by imported standing emergence plus collapse of admissibility-
preserving auxiliary refinements.
-/
theorem ATSImportedUniquenessDependencyStatement
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (ρ : α → ATSRole)
  (h_emergence :
    ∀ a : α,
      standing S a ↔
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_tensor_gatework :
    ∀ a : α,
      tensor_region ρ a →
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_tensor_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      tensor_region ρ a) :
  lawfully_equivalent_interiors
    (tensor_region ρ)
    (fun x => standing S x) := by
  intro a
  exact
    ATSTensorRegionCollapseStatement
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      ρ
      h_emergence
      h_tensor_gatework
      h_tensor_ext
      a

/--
ATS Theorem 5A, in fixed-domain Lean form.

Any role classifier whose tensor region is exactly the standing-bearing region
admits no fourth standing-bearing locus: every additional role predicate that
tracks the same standing-bearing work is lawfully equivalent to the tensor
region.
-/
theorem ATSRoleMinimalityAndExhaustivenessStatement
  {α : Type}
  (S : System α)
  (ρ : α → ATSRole)
  (R : α → Prop)
  (h_class : admissibility_preserving_role_classification S ρ)
  (hR_to_standing :
    ∀ a : α, R a → standing S a)
  (hStanding_to_R :
    ∀ a : α, standing S a → R a) :
  lawfully_equivalent_interiors R (tensor_region ρ) := by
  intro a
  constructor
  · intro hR
    have hS : standing S a := hR_to_standing a hR
    exact (h_class a).mpr hS
  · intro hTensor
    have hS : standing S a := (h_class a).mp hTensor
    exact hStanding_to_R a hS

/--
ATS Theorem 5B, in the paper's advertised fixed-constraint form.

If a proposed selector leaves standing fixed and leaves tensor content fixed,
then it is lawfully equivalent to the existing tensor region and therefore does
not define a fourth standing-bearing role.
-/
theorem ATSSelectorCollapseStatement
  {α : Type}
  (S : System α)
  (ρ : α → ATSRole)
  (Selector : α → Prop)
  (h_class : admissibility_preserving_role_classification S ρ)
  (hSel_to_standing :
    ∀ a : α, Selector a → standing S a)
  (hStanding_to_sel :
    ∀ a : α, standing S a → Selector a) :
  lawfully_equivalent_interiors Selector (tensor_region ρ) := by
  exact
    ATSRoleMinimalityAndExhaustivenessStatement
      S
      ρ
      Selector
      h_class
      hSel_to_standing
      hStanding_to_sel

/--
No fourth standing-bearing ATS role.

Any additional same-scope role predicate that is claimed to carry exactly the
standing-bearing work is lawfully equivalent to the tensor region once the
imported ATS dependency statement is in place.
-/
theorem ATSNoFourthStandingBearingRoleStatement
  {α : Type}
  (S : System α)
  (ρ : α → ATSRole)
  (R : α → Prop)
  (h_tensor :
    ∀ a : α, tensor_region ρ a ↔ standing S a)
  (hR_to_standing :
    ∀ a : α, R a → standing S a)
  (hStanding_to_R :
    ∀ a : α, standing S a → R a) :
  lawfully_equivalent_interiors R (tensor_region ρ) := by
  intro a
  constructor
  · intro hR
    have hS : standing S a := hR_to_standing a hR
    exact (h_tensor a).mpr hS
  · intro hTensor
    have hS : standing S a := (h_tensor a).mp hTensor
    exact hStanding_to_R a hS

/--
ATS Theorem 5C, specialized to the already-fixed three-role language.

Two admissibility-preserving ATS role classifiers on the same carrier are
role-isomorphic once they induce the same standing-bearing tensor region.
-/
theorem ATSRoleFactorizationUniquenessStatement
  {α : Type}
  (S : System α)
  (ρ₁ ρ₂ : α → ATSRole)
  (h₁ : admissibility_preserving_role_classification S ρ₁)
  (h₂ : admissibility_preserving_role_classification S ρ₂)
  (h_anchor :
    ∀ a : α, anchor_region ρ₁ a ↔ anchor_region ρ₂ a)
  (h_skin :
    ∀ a : α, skin_region ρ₁ a ↔ skin_region ρ₂ a) :
  ats_role_isomorphic ρ₁ ρ₂ := by
  refine ⟨h_anchor, ?_, h_skin⟩
  intro a
  constructor
  · intro hT
    have hS : standing S a := (h₁ a).mp hT
    exact (h₂ a).mpr hS
  · intro hT
    have hS : standing S a := (h₂ a).mp hT
    exact (h₁ a).mpr hS

end MaleyLean
