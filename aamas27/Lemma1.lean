import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace NormAwarePrivacy

section Definitions

variable {α : Type*}

/-- Initial posterior-to-prior ratio. -/
def initialRatio
    (r₀ : α → ℝ)
    (p : α) : ℝ :=
  r₀ p

/-- Likelihood-ratio contribution of message `s`. -/
def messageRatio
    (r : ℕ → α → ℝ)
    (s : ℕ)
    (p : α) : ℝ :=
  r s p

/-- Complete posterior-to-prior ratio after messages `1,...,t`. -/
def historyRatio
    (r₀ : α → ℝ)
    (r : ℕ → α → ℝ)
    (t : ℕ)
    (p : α) : ℝ :=
  initialRatio r₀ p *
    Finset.prod (Finset.range t)
      (fun s => messageRatio r (s + 1) p)

end Definitions


section PML

variable {α : Type*}

/-- Initial PML. -/
def initialPML
    (P : Finset α)
    (hP : P.Nonempty)
    (r₀ : α → ℝ) : ℝ :=
  P.sup' hP
    (fun p => Real.log (initialRatio r₀ p))

/-- Leakage contribution of message `s`. -/
def messageLeakage
    (P : Finset α)
    (hP : P.Nonempty)
    (r : ℕ → α → ℝ)
    (s : ℕ) : ℝ :=
  P.sup' hP
    (fun p =>
      Real.log (messageRatio r s p))

/-- History-level PML. -/
def historyPML
    (P : Finset α)
    (hP : P.Nonempty)
    (r₀ : α → ℝ)
    (r : ℕ → α → ℝ)
    (t : ℕ) : ℝ :=
  P.sup' hP
    (fun p =>
      Real.log (historyRatio r₀ r t p))

end PML


section Logarithms

variable {α : Type*}

/--
Logarithm of a finite product equals the sum of logarithms,
provided all factors are positive.
-/
lemma log_finset_prod
    (s : Finset α)
    (f : α → ℝ)
    (hpos : ∀ x ∈ s, 0 < f x) :
    Real.log (s.prod f)
      =
    s.sum (fun x => Real.log (f x)) := by

  classical

  induction s using Finset.induction_on with
  | empty =>
      simp

  | @insert a s ha ih =>
      have ha_pos : 0 < f a := by
        exact hpos a (by simp)

      have hs_pos : ∀ x ∈ s, 0 < f x := by
        intro x hx
        exact hpos x (by simp [hx])

      rw [Finset.prod_insert ha]
      rw [Finset.sum_insert ha]

      rw [Real.log_mul]

      · rw [ih hs_pos]

      · exact ne_of_gt ha_pos

      · exact ne_of_gt (Finset.prod_pos hs_pos)


/--
Logarithmic decomposition of the complete history ratio.
-/
lemma history_log_decomposition
    (r₀ : α → ℝ)
    (r : ℕ → α → ℝ)
    (t : ℕ)
    (p : α)
    (hpos₀ : 0 < initialRatio r₀ p)
    (hpos :
      ∀ s ∈ Finset.range t,
        0 < messageRatio r (s + 1) p) :
    Real.log (historyRatio r₀ r t p)
      =
    Real.log (initialRatio r₀ p) +
      Finset.sum (Finset.range t)
        (fun s =>
          Real.log (messageRatio r (s + 1) p)) := by

  unfold historyRatio

  rw [Real.log_mul]

  · rw [log_finset_prod
      (s := Finset.range t)
      (f := fun s => messageRatio r (s + 1) p)
      hpos]

  · exact ne_of_gt hpos₀

  · exact ne_of_gt (Finset.prod_pos hpos)

end Logarithms


section Supremum

variable {α : Type*}

/--
For every `p ∈ P`, the value of `f p` is bounded by the finite
supremum of `f` over the nonempty finite set `P`.
-/
lemma le_finset_sup
    (P : Finset α)
    (hP : P.Nonempty)
    (f : α → ℝ)
    {p : α}
    (hp : p ∈ P) :
    f p ≤ P.sup' hP f := by

  exact Finset.le_sup' f hp

end Supremum


section MainTheorem

variable {α : Type*}

/--
History-level PML accumulation.

If the logarithm of the complete posterior-to-prior ratio factorizes
into the initial log-ratio plus the sum of per-message log-ratios, then

  L(t) ≤ L(0) + Σₛ λ(s).
-/
lemma history_level_pml_accumulation
    (P : Finset α)
    (hP : P.Nonempty)
    (r₀ : α → ℝ)
    (r : ℕ → α → ℝ)
    (t : ℕ)

    (h_factor :
      ∀ p,
        Real.log (historyRatio r₀ r t p)
          =
        Real.log (initialRatio r₀ p) +
          Finset.sum (Finset.range t)
            (fun s =>
              Real.log (messageRatio r (s + 1) p))) :

    historyPML P hP r₀ r t
      ≤
    initialPML P hP r₀ +
      Finset.sum (Finset.range t)
        (fun s =>
          messageLeakage P hP r (s + 1)) := by

  classical

  unfold historyPML
  unfold initialPML
  unfold messageLeakage

  apply Finset.sup'_le hP

  intro p hp

  have hdecomp :
      Real.log (historyRatio r₀ r t p)
        =
      Real.log (initialRatio r₀ p) +
        Finset.sum (Finset.range t)
          (fun s =>
            Real.log (messageRatio r (s + 1) p)) := by

    exact h_factor p

  rw [hdecomp]

  have h0 :
      Real.log (initialRatio r₀ p)
        ≤
      P.sup' hP
        (fun p =>
          Real.log (initialRatio r₀ p)) := by

    exact le_finset_sup
      P
      hP
      (fun p =>
        Real.log (initialRatio r₀ p))
      hp

  have hsum :
      Finset.sum (Finset.range t)
          (fun s =>
            Real.log (messageRatio r (s + 1) p))
        ≤
      Finset.sum (Finset.range t)
        (fun s =>
          P.sup' hP
            (fun p =>
              Real.log (messageRatio r (s + 1) p))) := by

    apply Finset.sum_le_sum

    intro s hs

    exact le_finset_sup
      P
      hP
      (fun p =>
        Real.log (messageRatio r (s + 1) p))
      hp

  linarith


/--
Zero-initial-history corollary.

If the initial posterior-to-prior ratio equals one for every
private parameter in `P`, then the initial PML is zero.
-/
lemma history_level_pml_accumulation_zero_initial
    (P : Finset α)
    (hP : P.Nonempty)
    (r₀ : α → ℝ)
    (r : ℕ → α → ℝ)
    (t : ℕ)

    (h_factor :
      ∀ p,
        Real.log (historyRatio r₀ r t p)
          =
        Real.log (initialRatio r₀ p) +
          Finset.sum (Finset.range t)
            (fun s =>
              Real.log (messageRatio r (s + 1) p)))

    (h_initial :
      ∀ p ∈ P,
        initialRatio r₀ p = 1) :

    historyPML P hP r₀ r t
      ≤
    Finset.sum (Finset.range t)
      (fun s =>
        messageLeakage P hP r (s + 1)) := by

  have h_initial_pml :
      initialPML P hP r₀ = 0 := by

    unfold initialPML

    apply le_antisymm

    · /-
        Upper bound: every element of P has initial log-ratio zero.
      -/
      apply Finset.sup'_le hP

      intro p hp

      rw [h_initial p hp]

      simp

    · /-
        Lower bound: choose one element of P.
      -/
      have hex : ∃ p₀, p₀ ∈ P := hP

      obtain ⟨p₀, hp₀⟩ := hex

      have hp₀_le :
          Real.log (initialRatio r₀ p₀)
            ≤
          P.sup' hP
            (fun p =>
              Real.log (initialRatio r₀ p)) := by

        exact le_finset_sup
          P
          hP
          (fun p =>
            Real.log (initialRatio r₀ p))
          hp₀

      have hp₀_zero :
          Real.log (initialRatio r₀ p₀) = 0 := by

        rw [h_initial p₀ hp₀]

        simp

      calc
        (0 : ℝ)
            = Real.log (initialRatio r₀ p₀) := hp₀_zero.symm
        _ ≤
          P.sup' hP
            (fun p =>
              Real.log (initialRatio r₀ p)) := hp₀_le

  have hmain :
      historyPML P hP r₀ r t
        ≤
      initialPML P hP r₀ +
        Finset.sum (Finset.range t)
          (fun s =>
            messageLeakage P hP r (s + 1)) := by

    exact history_level_pml_accumulation
      P
      hP
      r₀
      r
      t
      h_factor

  rw [h_initial_pml] at hmain

  simpa using hmain

end MainTheorem

end NormAwarePrivacy
