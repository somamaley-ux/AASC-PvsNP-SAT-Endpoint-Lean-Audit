import MaleyLean.NoSilentRedescription

namespace MaleyLean

structure ScopeRelativeFixation (Scope α : Type) where
  licensedFixation : Scope → Redescription α α → Prop
  independentlyAdmissible : Scope → Redescription α α → Prop

def fixation_extension
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (T : Redescription α α) : Prop :=
  F.licensedFixation source T ∧ target ≠ source

def illicit_scope_transport
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (T : Redescription α α) : Prop :=
  fixation_extension F source target T ∧
  ¬ F.independentlyAdmissible target T

theorem fixation_extension_is_illicit_without_fresh_admissibility
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (T : Redescription α α)
  (h_ext : fixation_extension F source target T)
  (h_no_fresh : ¬ F.independentlyAdmissible target T) :
  illicit_scope_transport F source target T := by
  exact And.intro h_ext h_no_fresh

theorem scope_relative_fixation_is_nontransferable
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (T : Redescription α α)
  (h_illicit : illicit_scope_transport F source target T) :
  ¬ F.independentlyAdmissible target T := by
  exact h_illicit.2

theorem illicit_scope_transport_forces_silent_failure
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (S₁ S₂ : System α)
  (T : Redescription α α)
  (h_illicit : illicit_scope_transport F source target T)
  (h_failure :
    illicit_scope_transport F source target T →
    silent_redescription_failure S₁ S₂ T) :
  silent_redescription_failure S₁ S₂ T := by
  exact h_failure h_illicit

theorem illicit_scope_transport_blocks_legality
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (S₁ S₂ : System α)
  (T : Redescription α α)
  (h_illicit : illicit_scope_transport F source target T)
  (h_failure :
    illicit_scope_transport F source target T →
    silent_redescription_failure S₁ S₂ T) :
  ¬ redescription_legal S₁ S₂ T := by
  exact
    silent_redescription_failure_blocks_legality
      S₁
      S₂
      T
      (h_failure h_illicit)

theorem illicit_scope_transport_implies_terminal_standing_failure
  {Scope α : Type}
  (F : ScopeRelativeFixation Scope α)
  (source target : Scope)
  (S₁ S₂ : System α)
  (T : Redescription α α)
  (h_illicit : illicit_scope_transport F source target T)
  (h_failure :
    illicit_scope_transport F source target T →
    silent_redescription_failure S₁ S₂ T) :
  ∃ x, standing S₁ x ∧ ¬ standing S₂ (T x) := by
  exact h_failure h_illicit

end MaleyLean
