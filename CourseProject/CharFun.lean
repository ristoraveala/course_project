import Mathlib

open NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators Topology Filter Complex
open Measure
open scoped Real

/- We will prove general lemmas about characteristic functions of (Borel) probability measures on ℝ.
   The two key (difficult) results are:
      - if a random variable X has n moments, then the characteristic function φ
        of the law of X is n times continuously differentiable and φ⁽ⁿ⁾(0) = iⁿ 𝔼 Xⁿ ;
      - if the characteristic functions of μₙ converge poinwise to the characteristic function of a
        probability measure μ, then μₙ → μ in law.
   Other results that we need will be easier to prove and we will handle them first. -/

-- We fix, once and for all, a probability measure μ on ℝ.
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma charFun_zero_eq_one : charFun μ 0 = 1 := by
  rw[charFun_zero μ]
  simp

lemma charFun_cts : Continuous (charFun μ) := by
  apply continuous_of_dominated
  have : ∀ (x : ℝ), AEStronglyMeasurable (fun a ↦ cexp ((inner ℝ a x) * I)) μ := by
    measurability
  apply this
  have : ∀ (x : ℝ), ∀ᵐ (a : ℝ) ∂μ, ‖cexp ((inner ℝ a x) * I)‖ ≤ 1 := by
    intro x
    apply Filter.Eventually.of_forall
    intro y
    rw [← Complex.norm_exp_ofReal_mul_I (inner ℝ y x)]
  apply this
  apply integrable_const 1
  apply Filter.Eventually.of_forall
  intro x
  continuity

lemma charFun_transformation (a b : ℝ) :
  charFun (map (fun x ↦ a * x + b) μ) = fun t:ℝ ↦ (cexp (I*b*t)) * charFun μ (a*t) := by
  ext t
  rw[charFun,charFun]
  rw [← integral_const_mul (cexp (I * (b:ℝ)*(t:ℝ))) (fun x ↦ (cexp (inner ℝ x (a * t) * I)))]
  have fun_measurable : AEStronglyMeasurable (fun x ↦ cexp (↑(inner ℝ x t) * I)) (map (fun x ↦ a * x + b) μ) := by measurability
  have transform_measurable : AEMeasurable (fun x ↦ a * x + b) μ := by measurability
  rw [integral_map transform_measurable fun_measurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  simp
  intro x
  rw [← Complex.exp_add]
  apply congrArg cexp
  grind

lemma charFun_nth_derivative (n:ℕ) (moments : Integrable (fun x ↦ |x|^n) μ) :
  ContDiff ℝ n (charFun μ) ∧ iteratedDeriv n (charFun μ) = fun t:ℝ ↦ (I:ℂ)^n * μ[fun x ↦ (x:ℝ)^n * cexp (x * t * I)] := by

    sorry

lemma charFun_nth_derivative_zero (n:ℕ) (moments : Integrable (fun x ↦ |x|^n) μ) :
  iteratedDeriv n (charFun μ) 0 = (I:ℂ)^n * μ[fun x ↦ (x:ℝ)^n] := by
  have := (charFun_nth_derivative μ n moments).right
  rw [congr_fun this 0]
  simp

/- TODO: add Taylor expansion (easy consequence of the previous result), factorisation of a sum
   of independent RV's, and an application that gives the convergence to Gaussian characteristic
   function in the CLT. Also, maybe prove the derivative theorem in a more elementary fashion? -/
