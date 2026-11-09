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

lemma charFun_zero_eq_one : charFun μ 0 = 1 := by simp [charFun_zero μ]

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
  (hf : f = (fun θ:ℝ ↦ (fun x:ℝ ↦ ∑ k ∈ Icc 0 n, ((c k) * θ ^ k * x ^k) + θ ^ n * R θ x) ))
  (R_bdd : ∃ C₁:ℝ, ∀ θ x : ℝ, ‖R θ x‖ ≤ |C₁| * |x|^n)
  (R_cts : Continuous (Function.uncurry R))
  (R_zero : ∀ x:ℝ, R 0 x = 0)
  (moments : Integrable (fun x ↦ |x|^n) μ) :
  ∃ ε : ℝ → ℂ,
  (fun θ:ℝ ↦ ∫ x, f θ x ∂μ) = (fun θ:ℝ ↦ ∑ k ∈ Icc 0 n, ((c k) * θ ^ k * ∫ x, x^k ∂μ) + θ^n * ε θ)
  ∧ Continuous ε
  ∧ ε 0 = 0 := by
  obtain ⟨C₁,pC₁⟩ := R_bdd
  -- We use the obvious remainder function
  set ε := fun θ:ℝ ↦ ∫ x, R θ x ∂μ with ε_def
  use ε
  constructor
  · -- At first we prove that the remainder formula is valid.
    ext θ
    rw [ε_def]

    -- We need to apply the linearity of integral; there is some work to be done because all of the relevant lemmas need integrability.
    have : ∑ k ∈ Icc 0 n, (c k * θ ^ k * ∫ (x : ℝ), x^k ∂μ) + (θ:ℝ) ^ n * ∫ (x : ℝ), R θ x ∂μ
      = ∫ x, ((∑ k ∈ Icc 0 n, (c k)* θ ^ k * x^k) + (θ:ℝ) ^ n * R θ x )∂μ := by

      -- We prove that each term of the sum is integrable.
      have terms_integrable : ∀ k ∈ Icc 0 n , Integrable (fun x:ℝ ↦ (c k) * θ ^ k * x ^ k) μ := by
        intro k hk
        apply Integrable.const_mul
        have : AEStronglyMeasurable (fun x:ℝ ↦ (x:ℂ) ^ k) μ := by measurability
        apply (integrable_norm_iff this).mp
        rw [show (fun a:ℝ ↦ ‖(a:ℂ) ^ k‖) = fun a:ℝ ↦ |a|^k by ext a; simp]
        exact integrable_norm_pow_of_le aestronglyMeasurable_id (Finset.mem_Icc.mp hk).2 moments

      -- It is an easy consequence of the previous result that the sum of the terms is integrable.
      have sum_integrable : Integrable (fun x:ℝ ↦ ∑ k ∈ Icc 0 n , (c k) * θ ^ k * x ^ k) μ
        := integrable_finsetSum (Icc 0 n) terms_integrable

      -- and finally the remainder function must be shown to be integrable, this is what the condition "moments" is for.
      have remainder_integrable : Integrable (fun x:ℝ ↦ (θ:ℝ) ^ n * R θ x) μ := by
        apply Integrable.const_mul
        have bound_is_integrable : Integrable (fun x ↦ |C₁| * |x|^n) μ := by
          apply Integrable.const_mul ; exact moments
        have Rθ_AEStronglymeasurable : AEStronglyMeasurable (R θ) μ := by measurability
        have ae_bdd : ∀ᵐ (a : ℝ) ∂μ, ‖R θ a‖ ≤ ‖|C₁| * |a| ^ n‖ := by
          apply Filter.Eventually.of_forall
          simp
          exact pC₁ θ
        exact Integrable.mono bound_is_integrable Rθ_AEStronglymeasurable ae_bdd

      -- Now we can use the linearity of integral.
      simp [integral_add sum_integrable remainder_integrable,
        integral_const_mul (L := ℂ) (θ ^ n) (R θ),
        integral_finsetSum (Icc 0 n) terms_integrable]

      -- Both sides of the equality are expressed as a sum over k, by Finset.sum_congr we reduce into comparison of each term in the sums.
      have : Icc 0 n = Icc 0 n := rfl
      apply sum_congr this

      intro k hk
      rw [show c k * (θ:ℝ) ^ k * (∫ (x : ℝ), x ^ k ∂μ : ℝ) = c k * ∫ x, θ ^ k * x ^k ∂μ by simp [integral_const_mul, mul_assoc]]

      -- Next we will use linearity of intergal and integral_congr_ae to reduce to the claim that the integrands agree.
      have : ∫ (x : ℝ), θ ^ k * x ^ k ∂μ = ∫ (x : ℝ), (θ:ℂ)^k * (x:ℂ)^k ∂μ := by
        rw [show (fun x:ℝ ↦ (θ:ℂ)^k * (x:ℂ)^k)= (fun x:ℝ ↦ ↑ (θ ^ k * x ^ k)) by ext x; simp, integral_complex_ofReal]
      rw [this, ← integral_const_mul (μ := μ) (c k) (fun x:ℝ ↦ θ ^ k * x^k)]

      apply integral_congr_ae
      apply Filter.Eventually.of_forall

      -- Now field_simp does the trick, and we have proven the linearity.
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
      apply continuous_of_dominated -- Now we must prove that the conditions of the theorem are met.
      -- At first: ∀ (x : ℝ), AEStronglyMeasurable (R x) μ
      measurability
      -- Then: the bound
      have : ∀ (θ : ℝ), ∀ᵐ (x : ℝ) ∂μ, ‖R θ x‖ ≤ |C₁| * |x|^n := by
        intro θ
        apply Filter.Eventually.of_forall
        exact pC₁ θ
      exact this
      -- Then: the bound is integrable
      apply Integrable.const_mul ; exact moments
      apply Filter.Eventually.of_forall
      intro x
      exact Continuous.uncurry_right x R_cts
    · have : ε = fun θ:ℝ ↦ ∫ x, R θ x ∂μ := rfl
      simp [this, R_zero]

-- now we prove the following nice representation for the map eⁱᵗ.
lemma exp_it_taylor : (fun θ:ℝ ↦ (fun x:ℝ ↦ cexp (inner ℝ θ x * I) ))
  = fun θ:ℝ ↦ (fun x:ℝ ↦ 1 + I * x * θ - (1/2) * θ ^ 2 * x ^2
          - θ ^2 * ∫ u in 0..x, (∫ v in 0..u,  cexp (I*θ*v) - 1 ∂volume) ∂volume) := by
    ext θ x
    #check integral_exp_mul_complex
    #check taylor_integral_remainder
    sorry

-- Now we obtain the Taylor expansion of a characteristic function for a measure with two moments.
lemma snd_taylor_charFun (snd_moment : Integrable (fun x:ℝ ↦ |x|^2) μ) :
  ∃ ε : ℝ → ℂ, Continuous ε ∧ ε 0 = 0
  ∧ charFun μ = fun (t:ℝ) ↦ 1 + I * t * ∫ x, x ∂μ - (1/2) * t ^2 * ∫ x, x^2 ∂μ + t^2 * ε t := by

  set R := fun θ:ℝ ↦ (fun x:ℝ ↦ - ∫ u in 0..x, (∫ v in 0..u,  cexp (I*θ*v) - 1 ∂volume) ∂volume) with R_def

  have R_bdd : ∃ C₁:ℝ, ∀ θ x : ℝ, ‖R θ x‖ ≤ |C₁| * |x|^2 := by
    use 2
    intro θ x
    simp [R_def]
    -- We first prove the inner bound
    have : ∀ u ∈ Set.uIoc 0 x, ‖∫ (v : ℝ) in 0..u, cexp (I * ↑θ * ↑v) - 1‖ ≤ 2 * |x| := by
      intro u hu
      have : ∀ v ∈ Set.uIoc 0 u, ‖cexp (I * ↑θ * v) - 1‖ ≤ 2 := by
        intro v hv
        apply le_trans (norm_sub_le_norm_sub_add_norm_sub (cexp (I * ↑θ * v)) 0 1)
        simp
        have : ‖cexp (I * θ * v)‖ = 1 := by
          rw [show cexp (I * θ * v) = cexp (I * ↑(θ * v)) by simp; rw [mul_assoc]]
          exact norm_exp_I_mul_ofReal (θ * v)
        rw[this]
        grind
      have := intervalIntegral.norm_integral_le_of_norm_le_const this
      apply le_trans this
      grind

    have integral_bd := intervalIntegral.norm_integral_le_of_norm_le_const this

    simp [show 2 * |x| * |x| = 2 * x^2 by grind] at integral_bd
    exact integral_bd
  have R_cts : Continuous (Function.uncurry R) := by fun_prop
  have R_zero : ∀ x:ℝ, R 0 x = 0 := by
    intro x
    rw [R_def]
    simp

  -- c 0 = 1, c 1 = I, c 2 = -1/2, and c n = 0 otherwise
  set c := fun n:ℕ ↦ (1 - n) ⊔ 0 + n * ((2-n) ⊔ 0) * I + ((n-1) ⊔ 0) * ((3-n) ⊔ 0) * (- 1/2) with c_def

  set f := (fun θ:ℝ ↦ (fun x:ℝ ↦ cexp (inner ℝ θ x * I))) with f_def
  have hf : f = (fun θ:ℝ ↦ (fun x:ℝ ↦ ∑ k ∈ Icc 0 2, ((c k) * θ ^ k * x ^k) + θ ^ 2 * R θ x)) := by
    rw [f_def, exp_it_taylor]
    ext θ x
    simp [sum_Icc_succ_top,c_def, R_def]
    grind

  have tf := (taylor_of_param_integral (f := f) (R := R) μ 2 c hf R_bdd R_cts R_zero) snd_moment
  obtain ⟨ε,pε⟩ := tf
  use ε

  constructor
  · exact pε.right.left
  · constructor
    · exact pε.right.right
    · have ε_formula := (pε).left
      have : charFun μ = (fun θ ↦ ∫ (x : ℝ), f θ x ∂μ) := by
        ext θ
        simp [charFun,f_def]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        field_simp
      rw [← this] at ε_formula
      have : (fun θ:ℝ ↦ ∑ k ∈ Icc 0 2, c k * ↑θ ^ k * ↑(∫ (x : ℝ), x ^ k ∂μ) + ↑θ ^ 2 * ε θ)
        = (fun θ:ℝ ↦ 1 + I * θ * ∫ x, x ∂μ - (1/2) * θ ^2 * ∫ x, x^2 ∂μ + θ ^2 * ε θ) := by
        ext θ
        simp [sum_Icc_succ_top, c_def]
        grind
      rw [this] at ε_formula
      exact ε_formula

/- The next lemma is used in the proof of the CLT, which we phrased in terms of random variables rather than measures.
   Thus we prove it for the law of independent random variables. The result is essentially a restatement of the lemma
   iIndepFun.charFun_map_fun_sum_eq_prod, but we just state it in a slightly more convenient form. -/

lemma indep_sum_charFun {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : ℕ → Ω → ℝ}
  (measurable : ∀ (j:ℕ), AEMeasurable (Y j)) (indep : iIndepFun Y ℙ) (n : ℕ) :
    charFun (map (fun ω ↦ ∑ k : Icc 1 n, Y k ω) ℙ) = ∏ k : Icc 1 n, charFun (map (Y k) ℙ) := by
  have measurable' : ∀ j : Icc 1 n,  AEMeasurable (Y j) := by intro j ; exact measurable j
  have indep' : iIndepFun (fun i:Icc 1 n ↦ Y i) ℙ := iIndepFun_iff_finset.mp indep (Icc 1 n)
  exact iIndepFun.charFun_map_fun_sum_eq_prod measurable' indep'
