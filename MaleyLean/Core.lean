namespace MaleyLean

structure System (α : Type) where
  admissible : α → Prop
  standing : α → Prop
  standing_implies_admissible :
    ∀ x : α, standing x → admissible x

def standing {α : Type} (S : System α) (x : α) : Prop :=
  S.standing x

def admissible {α : Type} (S : System α) (x : α) : Prop :=
  S.admissible x

theorem standing_self
  {α : Type} (S : System α) (x : α)
  (h : standing S x) : standing S x := by
  exact h

theorem admissible_of_standing
  {α : Type} (S : System α) (x : α)
  (h : standing S x) : admissible S x := by
  exact S.standing_implies_admissible x h

theorem no_both_standing_and_not_standing
  {α : Type} (S : System α) (x : α) :
  ¬ (standing S x ∧ ¬ standing S x) := by
  intro h
  exact h.2 h.1

theorem standing_unique
  {α : Type} (S : System α)
  (P : α → Prop)
  (h : ∀ x, P x ↔ standing S x) :
  P = standing S := by
  funext x
  apply propext
  exact h x

def Metric (α : Type) := α → Nat

def metric_respects_boundary {α : Type} (S : System α) (m : Metric α) : Prop :=
  ∀ x, ¬ standing S x → m x = 0

theorem nonstanding_metric_zero
  {α : Type} (S : System α) (m : Metric α)
  (h : metric_respects_boundary S m) (x : α)
  (hx : ¬ standing S x) :
  m x = 0 := by
  exact h x hx

theorem metrics_equal_if_equal_on_standing
  {α : Type} (S : System α) (m₁ m₂ : Metric α)
  (h₁ : metric_respects_boundary S m₁)
  (h₂ : metric_respects_boundary S m₂)
  (hag : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  funext x
  by_cases hx : standing S x
  · exact hag x hx
  · have hm1 : m₁ x = 0 := h₁ x hx
    have hm2 : m₂ x = 0 := h₂ x hx
    rw [hm1, hm2]

def Redescription (α β : Type) := α → β

def redescription_legal
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β) : Prop :=
  ∀ x, standing S₁ x → standing S₂ (f x)

theorem standing_preserved_under_legal_redescription
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hlegal : redescription_legal S₁ S₂ f)
  (x : α)
  (hx : standing S₁ x) :
  standing S₂ (f x) := by
  exact hlegal x hx

theorem redescription_illegal_if_standing_lost
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (x : α)
  (hx : standing S₁ x)
  (hfail : ¬ standing S₂ (f x)) :
  ¬ redescription_legal S₁ S₂ f := by
  intro hlegal
  have hpres : standing S₂ (f x) := hlegal x hx
  exact hfail hpres

theorem no_preservation_without_legality
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hnot : ¬ redescription_legal S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → standing S₂ (f x)) := by
  exact hnot

def Continuation (α : Type) := α → α

def continuation_legal
  {α : Type}
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (C : Continuation α) : Prop :=
  licensed_same_scope_continuation C

def continuation_diverges
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (a b : α) : Prop :=
  ∃ C : Continuation α,
    continuation_legal licensed_same_scope_continuation C ∧
    ((GoodD (StatusD (C a)) ∧ ¬ GoodD (StatusD (C b))) ∨
     (GoodD (StatusD (C b)) ∧ ¬ GoodD (StatusD (C a))))

theorem continuation_diverges_has_legal_witness
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (a b : α)
  (h :
    continuation_diverges
      StatusD
      GoodD
      licensed_same_scope_continuation
      a
      b) :
  ∃ C : Continuation α,
    continuation_legal licensed_same_scope_continuation C := by
  rcases h with ⟨C, hlegal, _hpost⟩
  exact ⟨C, hlegal⟩

end MaleyLean
