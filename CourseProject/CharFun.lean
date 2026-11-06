import Mathlib

open NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators Topology Filter Complex Finset
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


-- To prove our Taylor representation of a characteristic function, we first prove the following result from which the Taylor representation follows with ease.

lemma taylor_of_param_integral {f : ℝ → ℝ → ℂ} {R : ℝ → ℝ → ℂ} (n:ℕ) (c : ℕ → ℂ)
  (hf : f = (fun θ:ℝ ↦ (fun x:ℝ ↦ ∑ k ∈ Icc 1 n, ((c k) * θ ^ k * x ^k) + θ ^ n * R θ x) ))
  (R_bdd : ∃ C₁:ℝ, ∀ θ x : ℝ, ‖R θ x‖ ≤ C₁ * |x|^n)
  (R_cts : Continuous (Function.uncurry R))
  (R_zero : ∀ x:ℝ, R 0 x = 0)
  (moments : Integrable (fun x ↦ |x|^n) μ) :
  ∃ ε : ℝ → ℂ,
  (fun θ:ℝ ↦ ∫ x, f θ x ∂μ) = (fun θ:ℝ ↦ ∑ k ∈ Icc 1 n, ((c k) * θ ^ k * ∫ x, x^k ∂μ) + θ^n * ε θ)
  ∧ Continuous ε
  ∧ ε 0 = 0 := by
  obtain ⟨C₁,pC₁⟩ := R_bdd
  -- We use the obvious remainder function
  let ε := fun θ:ℝ ↦ ∫ x, R θ x ∂μ
  use ε
  constructor
  · -- At first we prove that the remainder formula is valid.
    ext θ
    have : ε θ = ∫ x, R θ x ∂μ := rfl
    rw [this]

    -- We need to apply the linearity of integral; there are some technicalities because all of the relvant lemmas need integrability.
    have : ∑ k ∈ Icc 1 n, (c k * θ ^ k * ∫ (x : ℝ), x^k ∂μ) + (θ:ℝ) ^ n * ∫ (x : ℝ), R θ x ∂μ = ∫ x, ((∑ k ∈ Icc 1 n, (c k)* θ ^ k * x^k) + (θ:ℝ) ^ n * R θ x )∂μ := by
      have terms_integrable : ∀ k ∈ Icc 1 n , Integrable (fun x:ℝ ↦ (c k) * θ ^ k * x ^ k) μ := by
        intro k hk
        apply Integrable.const_mul
        have : AEStronglyMeasurable (fun x:ℝ ↦ (x:ℂ) ^ k) μ := by measurability
        apply (integrable_norm_iff this).mp
        have : (fun a:ℝ ↦ ‖(a:ℂ) ^ k‖) = fun a:ℝ ↦ |a|^k := by ext a; simp
        rw [this]
        exact integrable_norm_pow_of_le aestronglyMeasurable_id (Finset.mem_Icc.mp hk).2 moments
      have sum_integrable : Integrable (fun x:ℝ ↦ ∑ k ∈ Icc 1 n , (c k) * θ ^ k * x ^ k) μ := integrable_finsetSum (Icc 1 n) terms_integrable
      have remainder_integrable : Integrable (fun x:ℝ ↦ (θ:ℝ) ^ n * R θ x) μ := by
        apply Integrable.const_mul
        have bound_is_integrable : Integrable (fun x ↦ |C₁| * |x|^n) μ := by
          apply Integrable.const_mul
          exact moments
        have Rθ_AEStronglymeasurable : AEStronglyMeasurable (R θ) μ := by
          measurability
        have ae_bdd : ∀ᵐ (a : ℝ) ∂μ, ‖R θ a‖ ≤ ‖|C₁| * |a| ^ n‖ := by
          apply Filter.Eventually.of_forall
          have bdd := pC₁ θ
          simp
          intro x
          have : C₁ * |x|^n ≤ |C₁| * |x|^n := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            exact le_abs_self C₁
            refine pow_nonneg ?_ n
            exact abs_nonneg x
          exact le_trans (bdd x) this
        exact Integrable.mono bound_is_integrable Rθ_AEStronglymeasurable ae_bdd
      rw [integral_add sum_integrable remainder_integrable]
      rw [integral_const_mul (L := ℂ) (θ ^ n) (R θ)]
      simp
      rw [integral_finsetSum (Icc 1 n) terms_integrable]

      -- Both sides of the equality are expressed as a sum over k, by Finset.sum_congr we reduce into comparison of each term in the sums.
      have : Icc 1 n = Icc 1 n := rfl
      apply Finset.sum_congr this

      intro k hk
      have : c k * (θ:ℝ) ^ k * (∫ (x : ℝ), x ^ k ∂μ : ℝ) = c k * ∫ x, θ ^ k * x ^k ∂μ := by
        rw [integral_const_mul (μ := μ) (θ ^ k) (fun x:ℝ ↦ x^k)]
        simp
        rw [mul_assoc]
      rw[this]
      /- Next we will use linearity of intergal and integral_congr_ae to reduce to the claim that the integrands agree.
         We have to do the following slightly annoying coercion to deal with the fact that the integral is a real number embedded into ℂ. -/
      have : ∫ (x : ℝ), θ ^ k * x ^ k ∂μ = ∫ (x : ℝ), (θ:ℂ)^k * (x:ℂ)^k ∂μ := by
        have : (fun x:ℝ ↦ (θ:ℂ)^k * (x:ℂ)^k)= (fun x:ℝ ↦ ↑ (θ ^ k * x ^ k)) := by
          ext x
          simp
        rw [this]
        rw [integral_complex_ofReal]
      rw [this]
      rw [← integral_const_mul (μ := μ) (c k) (fun x:ℝ ↦ θ ^ k * x^k)]

      apply integral_congr_ae
      apply Filter.Eventually.of_forall

      -- Now field_simp does the trick.
      intro x
      field_simp

    rw [this]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    rw[hf]
  · -- Now we prove continuity and the fact that ε 0 = 0.
    constructor
    · have : ε = fun θ:ℝ ↦ ∫ x, R θ x ∂μ := rfl
      rw[this]
      apply continuous_of_dominated
      intro x
      have : Continuous (R x) := Continuous.uncurry_left x R_cts
      exact Continuous.aestronglyMeasurable this
      have : ∀ (θ : ℝ), ∀ᵐ (x : ℝ) ∂μ, ‖R θ x‖ ≤ C₁ * |x|^n := by
        intro θ
        apply Filter.Eventually.of_forall
        intro x
        exact (pC₁ θ x)
      exact this
      apply Integrable.const_mul
      exact moments
      apply Filter.Eventually.of_forall
      intro x
      exact Continuous.uncurry_right x R_cts
    · have : ε = fun θ:ℝ ↦ ∫ x, R θ x ∂μ := rfl
      rw[this]
      simp [R_zero]



-- I want my money back, this lemma (in a more general form) should be in Mathlib!
lemma contDiff_succ_of_iteratedDeriv {f : ℝ → ℂ} {n:ℕ} (hf : ContDiff ℝ n f) (hn : ContDiff ℝ 1 (iteratedDeriv n f)) : ContDiff ℝ (n+1) f := sorry

lemma charFun_nth_derivative (n:ℕ) (moments : Integrable (fun x ↦ |x|^n) μ) :
  ContDiff ℝ n (charFun μ) ∧ iteratedDeriv n (charFun μ) = fun t:ℝ ↦ (I:ℂ)^n * μ[fun x ↦ (x:ℝ)^n * cexp (t * x * I)] := by
    induction n with
    | zero => -- use charFun_cts and simp
      constructor
      · apply contDiff_zero.mpr
        exact charFun_cts μ
      · rw [iteratedDeriv_zero]
        ext t
        rw [charFun]
        simp
    | succ n ih =>
      have : Integrable (fun x ↦ |x|^n) μ := sorry
      have ih' := ih this
      have nth_deriv : ∀ t:ℝ, HasDerivAt (fun (s:ℝ) ↦ ∫ x, x ^ n * cexp (s * x * I) ∂μ) (∫ x, I * x ^ (n+1) * cexp (t * x * I) ∂μ) t := sorry

      constructor
      · apply contDiff_succ_of_iteratedDeriv ih'.left
        rw [ih'.right]
        simp
        apply contDiff_const.mul

        apply contDiff_one_iff_deriv.mpr
        constructor
        · intro t
          exact HasDerivAt.differentiableAt (nth_deriv t)
        · have : deriv (fun (t:ℝ) ↦ ∫ (x : ℝ), x ^ n * cexp (t * x * I) ∂μ) = (fun (t:ℝ) ↦ ∫ x, I * x ^ (n+1) * cexp (t * x * I) ∂μ) := by
            ext t
            rw [← HasDerivAt.deriv (nth_deriv t)]
          rw [this]

          -- use this lemma, make all of the hypotheses work.
          #check continuous_of_dominated
          sorry
      · have : iteratedDeriv (n+1) (charFun μ) = fun t:ℝ ↦ (I:ℂ)^(n+1) * μ[fun x ↦ (x:ℝ)^(n+1) * cexp (t * x * I)] := by
          rw [iteratedDeriv_succ, ih'.right]
          ext t
          have der_formula := HasDerivAt.deriv (HasDerivAt.mul_const (nth_deriv t) (I ^ n))
          have : (fun y:ℝ ↦ (∫ (x : ℝ), x ^ n * cexp (y * x * I) ∂μ) * I ^ n) = (fun y:ℝ ↦ I ^ n * (∫ (x : ℝ), x ^ n * cexp (y * x * I) ∂μ)) := by
            ext t
            grind
          rw [this] at der_formula
          rw [mul_comm] at der_formula

          #check integral_const_mul (μ := μ) I (fun x:ℝ ↦ x ^ (n+1) * cexp (t * x * I))

          -- use deriv_hyp, move this into the other part of the constructor
          sorry
        exact this

lemma charFun_nth_derivative_zero (n:ℕ) (moments : Integrable (fun x ↦ |x|^n) μ) :
  iteratedDeriv n (charFun μ) 0 = (I:ℂ)^n * μ[fun x ↦ (x:ℝ)^n] := by
  have := (charFun_nth_derivative μ n moments).right
  rw [congr_fun this 0]
  simp

/- TODO: add Taylor expansion (easy consequence of the previous result), factorisation of a sum
   of independent RV's, and an application that gives the convergence to Gaussian characteristic
   function in the CLT. Also, maybe prove the derivative theorem in a more elementary fashion? -/
