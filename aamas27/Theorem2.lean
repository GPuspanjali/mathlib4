import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace NormAwarePrivacy

section MinimumDistortion

variable {Mechanism : Type*}

theorem minimum_distortion_norm_enforcement
    (feasible : Mechanism → Prop)
    (distortion : Mechanism → ℝ)
    (_h_feasible_nonempty :
      ∃ mu : Mechanism, feasible mu)
    (h_minimum_attained :
      ∃ mu_star : Mechanism,
        feasible mu_star ∧
        ∀ mu : Mechanism,
          feasible mu →
          distortion mu_star ≤ distortion mu) :
    ∃ mu_star : Mechanism,
      feasible mu_star ∧
      ∀ mu : Mechanism,
        feasible mu →
        distortion mu_star ≤ distortion mu := by

  exact h_minimum_attained

end MinimumDistortion

end NormAwarePrivacy
