import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
set_option linter.unusedSectionVars false
noncomputable section

namespace NormAwarePrivacy

section SequentialHistoryPML

variable {P M : Type*}
variable [Fintype P] [Fintype M] [Nonempty P]


/- ================================================================
   1. SEQUENTIAL PROBABILITY MODEL
   ================================================================ -/

structure SequentialProbabilityModel where
  prior : P → ℝ
  kernel : P → List M → M → ℝ

  prior_pos :
    ∀ p, 0 < prior p

  prior_normalized :
    ∑ p, prior p = 1

  kernel_pos :
    ∀ p h m, 0 < kernel p h m

  kernel_normalized :
    ∀ p h, ∑ m, kernel p h m = 1


/- ================================================================
   2. JOINT MASS AND HISTORY MASS
   ================================================================ -/

def jointMass
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P) : List M → ℝ
  | [] =>
      μ.prior p
  | m :: h =>
      jointMass μ p h * μ.kernel p h m


def historyMass
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M) : ℝ :=
  ∑ p, jointMass μ p h


def posterior
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M) : ℝ :=
  jointMass μ p h / historyMass μ h


def privatePrior
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P) : ℝ :=
  μ.prior p


def messageGivenPrivateHistory
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M)
    (m : M) : ℝ :=
  μ.kernel p h m


def messageGivenHistory
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M)
    (m : M) : ℝ :=
  historyMass μ (m :: h) / historyMass μ h


/- ================================================================
   3. POSITIVITY
   ================================================================ -/

lemma jointMass_pos
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M) :
    0 < jointMass μ p h := by

  induction h with

  | nil =>
      exact μ.prior_pos p

  | cons m h ih =>
      unfold jointMass
      exact mul_pos ih (μ.kernel_pos p h m)


def HistoryPositive
    (μ : SequentialProbabilityModel (P := P) (M := M)) : Prop :=
  ∀ h : List M, 0 < historyMass μ h


/- ================================================================
   4. BAYESIAN ONE-STEP FACTORIZATION
   ================================================================ -/

lemma bayesian_one_step
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M)
    (m : M)
    (h_history : 0 < historyMass μ h)
    (h_next : 0 < historyMass μ (m :: h)) :
    posterior μ p (m :: h) / privatePrior μ p
      =
    (posterior μ p h / privatePrior μ p) *
    (messageGivenPrivateHistory μ p h m /
      messageGivenHistory μ h m) := by

  have h_prior_ne :
      privatePrior μ p ≠ 0 := by
    unfold privatePrior
    exact ne_of_gt (μ.prior_pos p)

  have h_history_ne :
      historyMass μ h ≠ 0 :=
    ne_of_gt h_history

  have h_next_ne :
      historyMass μ (m :: h) ≠ 0 :=
    ne_of_gt h_next

  unfold posterior
  unfold privatePrior
  unfold messageGivenPrivateHistory
  unfold messageGivenHistory

  field_simp [h_prior_ne, h_history_ne, h_next_ne]

  simp [jointMass]


/- ================================================================
   5. POINTWISE LOGARITHMIC LEAKAGE
   ================================================================ -/

def pointwiseHistoryLoss
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M) : ℝ :=
  Real.log
    (posterior μ p h / privatePrior μ p)


def pointwiseMessageLeakage
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M)
    (m : M) : ℝ :=
  Real.log
    (messageGivenPrivateHistory μ p h m /
     messageGivenHistory μ h m)


lemma logarithmic_bayesian_one_step
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (p : P)
    (h : List M)
    (m : M)
    (h_history : 0 < historyMass μ h)
    (h_next : 0 < historyMass μ (m :: h)) :
    pointwiseHistoryLoss μ p (m :: h)
      =
    pointwiseHistoryLoss μ p h
      +
    pointwiseMessageLeakage μ p h m := by

  have h_factor :
      posterior μ p (m :: h) / privatePrior μ p
        =
      (posterior μ p h / privatePrior μ p) *
      (messageGivenPrivateHistory μ p h m /
        messageGivenHistory μ h m) :=
    bayesian_one_step
      μ p h m h_history h_next

  unfold pointwiseHistoryLoss
  unfold pointwiseMessageLeakage

  rw [h_factor]

  have h_old_ratio :
      0 < posterior μ p h / privatePrior μ p := by

    unfold posterior
    unfold privatePrior

    exact div_pos
      (div_pos
        (jointMass_pos μ p h)
        h_history)
      (μ.prior_pos p)

  have h_message_ratio :
      0 <
        messageGivenPrivateHistory μ p h m /
        messageGivenHistory μ h m := by

    unfold messageGivenPrivateHistory
    unfold messageGivenHistory

    exact div_pos
      (μ.kernel_pos p h m)
      (div_pos h_next h_history)

  rw [Real.log_mul]

  · exact ne_of_gt h_old_ratio

  · exact ne_of_gt h_message_ratio


/- ================================================================
   6. HISTORY-LEVEL PML
   ================================================================ -/

def historyPML
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M) : ℝ :=
  (Finset.univ : Finset P).sup'
    (Finset.univ_nonempty :
      (Finset.univ : Finset P).Nonempty)
    (fun p : P =>
      pointwiseHistoryLoss μ p h)


def messageLeakage
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M)
    (m : M) : ℝ :=
  (Finset.univ : Finset P).sup'
    (Finset.univ_nonempty :
      (Finset.univ : Finset P).Nonempty)
    (fun p : P =>
      pointwiseMessageLeakage μ p h m)


/- ================================================================
   7. BASIC SUPREMUM BOUNDS
   ================================================================ -/

lemma le_historyPML
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M)
    (p : P) :
    pointwiseHistoryLoss μ p h ≤ historyPML μ h := by

  unfold historyPML

  exact Finset.le_sup'
    (fun p : P =>
      pointwiseHistoryLoss μ p h)
    (Finset.mem_univ p)


lemma le_messageLeakage
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M)
    (m : M)
    (p : P) :
    pointwiseMessageLeakage μ p h m
      ≤
    messageLeakage μ h m := by

  unfold messageLeakage

  exact Finset.le_sup'
    (fun p : P =>
      pointwiseMessageLeakage μ p h m)
    (Finset.mem_univ p)


/- ================================================================
   8. ONE-STEP HISTORY-LEVEL PML
   ================================================================ -/

lemma historyPML_one_step
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h : List M)
    (m : M)
    (h_history : 0 < historyMass μ h)
    (h_next : 0 < historyMass μ (m :: h)) :
    historyPML μ (m :: h)
      ≤
    historyPML μ h + messageLeakage μ h m := by

  unfold historyPML
  unfold messageLeakage

  refine
    Finset.sup'_le
      (s := (Finset.univ : Finset P))
      (f := fun p : P =>
        pointwiseHistoryLoss μ p (m :: h))
      (Finset.univ_nonempty :
        (Finset.univ : Finset P).Nonempty)
      ?_

  intro p hp

  have h_pointwise :
      pointwiseHistoryLoss μ p (m :: h)
        =
      pointwiseHistoryLoss μ p h
        +
      pointwiseMessageLeakage μ p h m := by

    exact logarithmic_bayesian_one_step
      μ p h m h_history h_next

  have h_old :
      pointwiseHistoryLoss μ p h
        ≤
      historyPML μ h := by

    exact le_historyPML μ h p

  have h_msg :
      pointwiseMessageLeakage μ p h m
        ≤
      messageLeakage μ h m := by

    exact le_messageLeakage μ h m p

  rw [h_pointwise]

  exact add_le_add h_old h_msg


/- ================================================================
   9. HISTORY UPDATE
   ================================================================ -/

def historyAfter
    (h : List M) :
    List M → List M
  | [] =>
      h

  | m :: msgs =>
      historyAfter (m :: h) msgs


/- ================================================================
   10. ACCUMULATED LEAKAGE
   ================================================================ -/

def historyLeakageSumFrom
    (μ : SequentialProbabilityModel (P := P) (M := M))
    :
    List M → List M → ℝ
  | _h, [] =>
      0

  | h, m :: msgs =>
      messageLeakage μ h m
        +
      historyLeakageSumFrom μ (m :: h) msgs


/- ================================================================
   11. MAIN ACCUMULATION LEMMA
   ================================================================ -/

lemma history_level_pml_accumulation
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h0 : List M)
    (msgs : List M)
    (h_positive : HistoryPositive μ) :
    historyPML μ (historyAfter h0 msgs)
      ≤
    historyPML μ h0
      +
    historyLeakageSumFrom μ h0 msgs := by

  induction msgs generalizing h0 with

  | nil =>

      simp [historyAfter, historyLeakageSumFrom]

  | cons m msgs ih =>
    have h_history :
        0 < historyMass μ h0 :=
      h_positive h0

    have h_next :
        0 < historyMass μ (m :: h0) :=
      h_positive (m :: h0)

    have h_step :
        historyPML μ (m :: h0)
         ≤
        historyPML μ h0
         +
        messageLeakage μ h0 m :=
      historyPML_one_step
        μ
        h0
        m
        h_history
        h_next

    have h_ind :
        historyPML μ (historyAfter (m :: h0) msgs)
          ≤
        historyPML μ (m :: h0)
          +
        historyLeakageSumFrom μ (m :: h0) msgs :=
      ih (h0 := m :: h0)

    simp only [historyAfter, historyLeakageSumFrom]

    calc
      historyPML μ
          (historyAfter (m :: h0) msgs)
          ≤
        historyPML μ (m :: h0)
          +
        historyLeakageSumFrom μ (m :: h0) msgs :=
        h_ind

      _ ≤
        historyPML μ h0
          +
        messageLeakage μ h0 m
          +
        historyLeakageSumFrom μ (m :: h0) msgs := by
        exact add_le_add
          h_step
          (le_refl (historyLeakageSumFrom μ (m :: h0) msgs))

      _ =
        historyPML μ h0
          +
        (messageLeakage μ h0 m
          +
         historyLeakageSumFrom μ (m :: h0) msgs) := by
        ring


/- ================================================================
   12. ZERO-INITIAL-PML COROLLARY
   ================================================================ -/

lemma history_level_pml_accumulation_zero_initial
    (μ : SequentialProbabilityModel (P := P) (M := M))
    (h0 : List M)
    (msgs : List M)
    (h_positive : HistoryPositive μ)
    (h_initial_zero : historyPML μ h0 = 0) :
    historyPML μ (historyAfter h0 msgs)
      ≤
    historyLeakageSumFrom μ h0 msgs := by

  have h_main :
      historyPML μ (historyAfter h0 msgs)
        ≤
      historyPML μ h0
        +
      historyLeakageSumFrom μ h0 msgs :=
    history_level_pml_accumulation
      μ
      h0
      msgs
      h_positive

  rw [h_initial_zero] at h_main

  simpa using h_main


end SequentialHistoryPML

end NormAwarePrivacy
