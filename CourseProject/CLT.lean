import Mathlib
open MeasureTheory ProbabilityTheory Filter

-- We introduce a probability space
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- We introduce a sequence of random variables that is iid, and all elements have a second moment

variable {X : ℕ → Ω → ℝ} (meas : ∀ n, Measurable (X n))
  (iid : iIndepFun X ℙ)
  (snd_moments : ∀ n, MemLp (X n) 2 ℙ)

include iid snd_moments in
theorem CLT : TendstoInDistribution
  (fun (n:ℕ) ↦ fun ω ↦ (1/√(n * variance (X 1) ℙ)) * (∑ i ∈ Finset.Icc 1 n, (X i ω - ℙ[X i])))
    atTop id (fun n ↦ ℙ) (gaussianReal 0 1) := by
  sorry
