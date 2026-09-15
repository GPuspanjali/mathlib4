import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace NormAwarePrivacy

section PrivacyUtilityFeasibility

variable {Policy : Type*}

theorem norm_constrained_utility
    (feasible : Policy → Prop)
    (utility : Policy → ℝ)
    (U_min : ℝ)
    (_h_feasible_nonempty :
      ∃ pi : Policy, feasible pi)
    (h_max_attained :
      ∃ pi_star : Policy,
        feasible pi_star ∧
        ∀ pi : Policy,
          feasible pi →
          utility pi ≤ utility pi_star)
    (h_utility_feasible :
      ∃ pi_star : Policy,
        feasible pi_star ∧
        U_min ≤ utility pi_star) :
    (∃ U_star : ℝ,
        (∃ pi_star : Policy,
          feasible pi_star ∧
          utility pi_star = U_star) ∧
        ∀ pi : Policy,
          feasible pi →
          utility pi ≤ U_star)
    ∧
    (∃ pi_star : Policy,
      feasible pi_star ∧
      U_min ≤ utility pi_star) := by

  obtain ⟨pi_max, h_pi_max_feasible, h_pi_maximal⟩ :=
    h_max_attained

  have h_max_exists :
      ∃ U_star : ℝ,
        (∃ pi_star : Policy,
          feasible pi_star ∧
          utility pi_star = U_star) ∧
        ∀ pi : Policy,
          feasible pi →
          utility pi ≤ U_star := by

    refine ⟨utility pi_max, ?_, ?_⟩

    · exact ⟨pi_max, h_pi_max_feasible, rfl⟩

    · intro pi h_pi
      exact h_pi_maximal pi h_pi

  exact ⟨h_max_exists, h_utility_feasible⟩

end PrivacyUtilityFeasibility

end NormAwarePrivacy
