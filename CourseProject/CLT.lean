import Mathlib
import CourseProject.CharFun.Basic
import CourseProject.CharFun.CharFunConvergence

open MeasureTheory Topology ProbabilityTheory Filter
open Complex

-- We introduce a probability space
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- We introduce a sequence of random variables that is iid, and all elements have a second moment
noncomputable section CLT

variable {X : ℕ → Ω → ℝ} (meas : ∀ n, Measurable (X n))
  (independence : iIndepFun X ℙ) (ident_distrib : ∀ i j : ℕ, IdentDistrib (X i) (X j) ℙ ℙ)
  (snd_moments : ∀ n, MemLp (X n) 2 ℙ) (snd_moment_nonzero : ∀ n:ℕ, ∫ ω , |X n ω|^2 ∂ℙ ≠ 0)

include meas independence ident_distrib snd_moments snd_moment_nonzero in
theorem CLT : TendstoInDistribution
  (fun (n:ℕ) ↦ fun ω ↦ (1/√(n * variance (X 1) ℙ)) * (∑ i : Finset.Icc 1 n, (X i ω - ℙ[X 1])))
    atTop id (fun n ↦ ℙ) (gaussianReal 0 1) := by
  set v := variance (X 1) ℙ
  have v_ne_zero : v ≠ 0 := by sorry -- use snd_moment_nonzero
  set ℓ := fun n:ℕ ↦ (Measure.map (fun ω ↦ (1/√(n * variance (X 1) ℙ)) * (∑ i : Finset.Icc 1 n, (X i ω - ℙ[X 1]))) ℙ) with hℓ
  set ν := fun i:ℕ ↦ (Measure.map (fun ω ↦ (X i ω - ℙ[X 1])) ℙ) with hν
  have ν_const : ∀ i, ν i = ν 1 := by
    rw [hν]
    intro i
    apply IdentDistrib.map_eq
    exact IdentDistrib.sub_const (ident_distrib i 1) (∫ (ω : Ω), X 1 ω)
  have : ∀ t:ℝ, Tendsto (fun n:ℕ ↦ (charFun (ℓ n) t)) atTop (𝓝 (cexp (-t/2))) := by
    intro t
    sorry
  sorry
