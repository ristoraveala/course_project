import Mathlib
import CourseProject.CharFun.Basic
import CourseProject.CharFun.CharFunConvergence
import CourseProject.CharFun.CharFunCLTLimit

open MeasureTheory Topology ProbabilityTheory Filter
open Complex

-- We introduce a probability space
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- We introduce a sequence of random variables that is iid, and all elements have a second moment
noncomputable section CLT

variable {X : ℕ → Ω → ℝ} (meas : ∀ n, Measurable (X n))
  (independence : iIndepFun X ℙ) (ident_distrib : ∀ i j : ℕ, IdentDistrib (X i) (X j) ℙ ℙ)
  (snd_moments : ∀ n, Integrable (fun x:ℝ ↦ |x|^2) (Measure.map (X n) ℙ))
  (variance_nonzero : ∫(x:ℝ) , |x|^2 ∂(Measure.map (fun ω ↦ X 1 ω - ℙ[X 1]) ℙ) ≠ 0)

include meas independence ident_distrib snd_moments variance_nonzero in
theorem CLT : Tendsto
  (fun (n:ℕ) ↦ (Measure.map (fun ω ↦ (1/√(n * variance (X 1) ℙ)) * (∑ i : Finset.Icc 1 n, (X i ω - ℙ[X 1]))) ℙ).toProbabilityMeasure)
    atTop (𝓝 (gaussianReal 0 1).toProbabilityMeasure) := by
  set v := ∫ (x : ℝ), |x| ^ 2 ∂Measure.map (fun ω ↦ X 1 ω - ℙ[X 1]) ℙ with hv
  have : variance (X 1) ℙ = v := by
    rw [hv]
    have meas_X1 : AEMeasurable (fun ω ↦ X 1 ω - ℙ[X 1]) := by measurability
    have measxsq : AEStronglyMeasurable (fun x:ℝ ↦ |x|^2) (Measure.map (fun ω ↦ X 1 ω - ℙ[X 1]) ℙ) := by measurability
    rw [integral_map meas_X1 measxsq, variance_eq_integral]
    simp
    measurability
  rw [this]
  have charFuns_converge :
    ∀ (t : ℝ), Tendsto (fun n:ℕ  ↦ charFun (Measure.map (fun ω ↦ 1 / √(↑n * v) * ∑ k:Finset.Icc 1 n, (X k ω - ℙ[X 1])) ℙ) t)
    atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
    intro t
    have convergence := iid_sum_to_cexp meas independence ident_distrib (snd_moments 1) variance_nonzero t
    rw [← hv] at convergence
    simp [charFun_gaussianReal (μ := 0) (v := 1)]
    simp [show cexp (-(t:ℂ) ^ 2 / 2) = cexp (-((t:ℂ) ^ 2 / 2)) by grind] at convergence
    exact convergence
  have gaussian_charFun := charFun_gaussianReal (μ := 0) (v := 1)
  simp at gaussian_charFun
  exact charFun_convergence (gaussianReal 0 1) charFuns_converge
