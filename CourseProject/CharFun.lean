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

noncomputable section general_lemmas

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

end general_lemmas


noncomputable section charFun_convergence

/- We prove in this section, that if the characteristic functions of a sequence (νₙ) converge pointwise to the
   characteristic funtion of (a probability measure) μ, then νₙ → μ as probability measures. -/

variable {ν : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (ν n)]

theorem charFun_convergence (charFuns_converge : ∀ t:ℝ, Tendsto (fun n ↦ (charFun (ν n) t)) atTop (𝓝 (charFun μ t))) :
  Tendsto (fun n ↦ (ν n).toProbabilityMeasure) atTop (𝓝 μ.toProbabilityMeasure) := by sorry

/- In the proof, the key idea is to prove the theorem first for a class of probability measures with densities (wrt
   the Lebesgue measure) and then do a mollification argument. -/

variable {p : ℕ → (ℝ → ℝ≥0∞)} (p_measurable : ∀ n, Measurable (p n)) (p_cts : ∀ n , Continuous (fun x:ℝ ↦ ((p n x).toReal:ℂ))) -- We take p n as the density of ν n.
variable {f : ℝ → ℝ≥0∞} (f_measurable : Measurable f) (f_cts : Continuous (fun x:ℝ ↦ ((f x).toReal:ℂ)))

lemma lintegral_of_density_eq_one {g : ℝ → ℝ≥0∞} (exists_density : withDensity volume g = μ) :
  ∫⁻ x:ℝ, g x ∂volume = 1 := by
  obtain ⟨g,pg⟩ := exists_density
  have : MeasurableSet (Set.univ : Set ℝ) := MeasurableSet.univ
  rw [← show ∫⁻ (x : ℝ) in Set.univ, g x = ∫⁻ (x : ℝ), g x by exact (setLIntegral_univ g)]
  rw [← withDensity_apply g MeasurableSet.univ]
  simp

lemma ae_finite_density {g : ℝ → ℝ≥0∞} (exists_density : withDensity volume g = μ) (hg : Measurable g) :
  ∀ᵐ (x : ℝ) ∂volume, g x < ∞ := by
  apply ae_lt_top hg
  rw [lintegral_of_density_eq_one μ exists_density]
  exact one_ne_top

lemma integral_of_density_eq_one {g : ℝ → ℝ≥0∞} (hg : Measurable g) (exists_density : withDensity volume g = μ) :
  ∫ x:ℝ, (g x).toReal ∂volume = 1 := by
  have : AEMeasurable g volume := Measurable.aemeasurable hg
  have := integral_toReal this (ae_finite_density μ exists_density hg)
  rw [lintegral_of_density_eq_one μ exists_density] at this
  rw[toReal_one] at this
  exact this

lemma integrable_density {g : ℝ → ℝ≥0∞} (hg : Measurable g) (exists_density : withDensity volume g = μ) :
  Integrable (fun x ↦ (g x).toReal) volume := by
  have : AEStronglyMeasurable (fun x ↦ (g x).toReal) volume := by
    have ae_st_meas : AEStronglyMeasurable g volume := Measurable.aestronglyMeasurable hg
    have := Measurable.ennreal_toReal hg
    exact Measurable.aestronglyMeasurable this
  apply (integrable_norm_iff this).mp
  have norm_ae_str_meas : AEStronglyMeasurable (fun x ↦ |(g x).toReal|) volume
    := Continuous.comp_aestronglyMeasurable continuous_abs this
  have : 0 ≤ᵐ[volume] fun x ↦ |(g x).toReal| := by
    apply Filter.Eventually.of_forall
    intro x
    simp
  apply (lintegral_ofReal_ne_top_iff_integrable norm_ae_str_meas this).mp
  have : (fun x:ℝ ↦ ENNReal.ofReal |(g x).toReal|) =ᵐ[volume] (fun x:ℝ ↦ g x) := by
    simp
    apply ofReal_toReal_ae_eq
    exact ae_finite_density μ exists_density hg
  rw [lintegral_congr_ae this]
  rw [lintegral_of_density_eq_one μ exists_density]
  exact one_ne_top

lemma integrable_density' {g : ℝ → ℝ≥0∞} (hg : Measurable g) (exists_density : withDensity volume g = μ) :
  Integrable (fun x ↦ ((g x).toReal:ℂ)) volume := by
  have := integrable_density μ hg exists_density
  exact Integrable.ofReal this

open FourierTransform

-- This lemma allows us to use the fourier transform lemmas for the characteristic function of a measure with a density.
lemma charFun_eq_fourier {g : ℝ → ℝ≥0∞} (hg : Measurable g) (exists_density : withDensity volume g = μ) :
  (fun t ↦ charFun μ (- 2*π*t)) = 𝓕 (fun x:ℝ ↦ (((g x).toReal):ℂ)) := by
    ext t
    rw [charFun, ← exists_density]
    simp [Real.fourier_eq]
    have ae_finite: (∀ᵐ (x : ℝ) ∂(Measure.restrict volume Set.univ), g x < ∞) := by
      apply ae_lt_top
      exact hg
      simp; push Not
      rw [lintegral_of_density_eq_one μ exists_density]
      exact one_ne_top
    have density_unwind := setIntegral_withDensity_eq_setIntegral_toReal_smul
            hg ae_finite (fun x:ℝ ↦ cexp (-(2*π*↑t * ↑x * I))) MeasurableSet.univ
    simp at density_unwind
    rw [density_unwind]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp [Real.fourierChar]
    field_simp
    have : (Circle.exp (2 * π *t * x))⁻¹ • ((g x).toReal:ℂ) = ((Circle.exp (2*π*t*x))⁻¹:ℂ) * ↑(g x).toReal := by
      rw [Circle.smul_def] ; simp
    simp [this, exp_neg]
    field_simp


lemma charFun_inversion {g : ℝ → ℝ≥0∞} (hg : Measurable g) (cts_g : Continuous (fun x ↦ ((g x).toReal:ℂ)))
  (exists_density : withDensity (volume:Measure ℝ) g = μ)
  (integrable_charFun : Integrable (charFun μ) volume):
  (fun x:ℝ ↦ ((g x).toReal:ℂ)) = fun x:ℝ ↦ ∫ ξ:ℝ, cexp (2*π*I * x * ξ) * charFun μ (-2*π*ξ) ∂volume := by
  ext x
  -- At first we rewrite the claim as a claim concerning Fourier inversion
  have : ∫ (v : ℝ), cexp (2 * ↑π * I * ↑x * ↑v) * charFun μ (-2 * π * v) ∂volume
    = ∫ (v : ℝ), cexp (↑((2:ℝ) * (π:ℝ) * inner ℝ v x) * I) • 𝓕 (fun x:ℝ ↦ (((g x).toReal):ℂ)) v ∂volume := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    simp
    rw [← charFun_neg (μ := μ) (2*π*ξ)]
    have := congr_fun (charFun_eq_fourier μ hg exists_density) ξ
    rw [← this]
    field_simp
  rw [this]
  have := Real.fourierInv_eq' (f := 𝓕 (fun x:ℝ ↦ (((g x).toReal):ℂ))) x
  rw [← this]
  apply Eq.symm
  -- Now we just use an existing lemma on Fourier inversion to finish the job.
  have fourier_is_integrable : Integrable (𝓕 (fun x:ℝ ↦ ((g x).toReal:ℂ))) volume := by
    rw [← charFun_eq_fourier μ hg exists_density]
    have : -2*π ≠ 0 := by norm_num
    exact Integrable.comp_mul_left' integrable_charFun this
  have density_is_integrable := integrable_density' (μ := μ) hg exists_density
  have := Continuous.fourierInv_fourier_eq cts_g density_is_integrable fourier_is_integrable
  exact congr_fun this x

include p_measurable p_cts f_measurable f_cts in
lemma charFun_pointwise_convergence_with_densities (charFuns_converge : ∀ t:ℝ, Tendsto (fun n ↦ (charFun (ν n) t)) atTop (𝓝 (charFun μ t)))
  (exists_densities_ν : ∀ n:ℕ, withDensity volume (p n) = (ν n)) (exists_density_μ : withDensity volume f = μ)
  (charFuns_dominated : ∃ g : ℝ → ℝ, Integrable g volume ∧ (∀ (n:ℕ) (t:ℝ), ‖charFun (ν n) t‖ ≤ g t) ∧ ∀ t, ‖charFun μ t‖ ≤ g t) :
  ∀ x : ℝ, Tendsto (fun n ↦ ((p n x).toReal - ((f x).toReal):ℂ)) atTop (𝓝 0) := by

  -- Some preliminary parts
  obtain ⟨g,pg⟩ := charFuns_dominated

  have charFuns_ν_integrable : ∀ n:ℕ, Integrable (charFun (ν n)) volume := by
    intro n
    have bdd : ∀ᵐ (x : ℝ) ∂volume, ‖charFun (ν n) x‖ ≤ g x := by
      apply Filter.Eventually.of_forall
      exact pg.right.left n
    have h_measurable : AEStronglyMeasurable (charFun (ν n)) volume := by measurability
    exact Integrable.mono' pg.left h_measurable bdd

  have charFun_μ_integrable : Integrable (charFun μ) volume := by
    have bdd :  ∀ᵐ (x : ℝ) ∂volume, ‖charFun μ x‖ ≤ g x := by
      apply Filter.Eventually.of_forall
      exact pg.right.right
    have h_measurable : AEStronglyMeasurable (charFun μ) volume := by measurability
    exact Integrable.mono' pg.left h_measurable bdd

  -- The main proof begins.
  intro x
  -- Now we apply the inversion formula.
  have : (fun n ↦ (p n x).toReal - ((f x).toReal:ℂ))
    = (fun n ↦ ∫ ξ:ℝ, cexp (2*π*I * x * ξ) * (charFun (ν n) (-2*π*ξ) - charFun μ (-2*π*ξ)) ∂volume) := by
    ext n
    have := charFun_inversion (ν n) (p_measurable n) (p_cts n) (exists_densities_ν n) (charFuns_ν_integrable n)
    rw [congr_fun this x]
    have := charFun_inversion μ f_measurable f_cts exists_density_μ charFun_μ_integrable
    rw [congr_fun this x]

    have cexp_bdd : ∀ᵐ (ξ : ℝ) ∂volume, ‖(fun ξ:ℝ ↦ cexp (2 * ↑π * I * ↑x* ↑ξ)) ξ‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ξ
      simp
      have : 2 * ↑π * I * ↑x* ↑ξ = I * ((2*π*x*ξ):ℝ) := by simp ; grind
      rw [this]
      have := norm_exp_I_mul_ofReal (2*π*x*ξ)
      exact le_of_eq this
    have cexp_meas : AEStronglyMeasurable (fun ξ:ℝ ↦ cexp (2 * ↑π * I * ↑x* ↑ξ)) volume := by measurability

    have integrable_n : Integrable (fun ξ:ℝ ↦ cexp (2 * ↑π * I * ↑x* ↑ξ) * charFun (ν n) (-2 * π * ξ)) volume := by
      have : Integrable (fun ξ:ℝ ↦ charFun (ν n) (-2 * π * ξ)) volume := by
        have : -2*π ≠ 0 := by norm_num
        exact Integrable.comp_mul_left' (charFuns_ν_integrable n) this
      exact Integrable.bdd_mul this cexp_meas cexp_bdd

    have integrable_μ : Integrable (fun ξ:ℝ ↦ cexp (2 * ↑π * I * ↑x * ↑ξ) * charFun μ (-2 * π * ξ)) volume := by
      have : Integrable (fun ξ:ℝ ↦ charFun μ (-2 * π * ξ)) volume := by
        have : -2*π ≠ 0 := by norm_num
        exact Integrable.comp_mul_left' charFun_μ_integrable this
      exact Integrable.bdd_mul this cexp_meas cexp_bdd

    rw [← integral_sub integrable_n integrable_μ]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    field_simp

  rw [this]
  have : ∫ x:ℝ, (0:ℂ) ∂volume = 0 := integral_zero ℝ ℂ
  rw [← this]

  -- The assumptions are so that we can now just use dominated convergence.
  apply tendsto_integral_filter_of_dominated_convergence
  apply Filter.Eventually.of_forall
  intro n
  measurability

  -- Then we prove that 2*g is the suitable bound.
  apply Filter.Eventually.of_forall
  intro n
  apply Filter.Eventually.of_forall
  intro t
  rw [Complex.norm_mul,
      show cexp (2 * ↑π * I * ↑x * ↑t) = cexp (I*((2 * π * x * t):ℝ)) by simp; field_simp,
      norm_exp_I_mul_ofReal, one_mul]
  apply le_trans (norm_sub_le (charFun (ν n) (-2 * π * t)) (charFun μ (-2 * π * t)))
  have : ‖charFun (ν n) (-2 * π * t)‖ + ‖charFun μ (-2 * π * t)‖ ≤ 2 * g (-2*π*t) := by
    have h1 := (add_le_add_left ((pg.right.left n) (-2*π*t)) ‖charFun μ (-2 * π * t)‖)
    have h2 := (add_le_add_right (pg.right.right (-2*π*t)) (g (-2*π*t)))
    have integrand_bd := le_trans h1 h2
    have : g (-2 * π * t) + g (-2 * π * t) = 2 * g (-2 * π * t) := Eq.symm (two_mul (g (-2 * π * t)))
    rw [this] at integrand_bd
    exact integrand_bd
  exact this

  -- The bound x ↦ 2*g(-2 * π x) must be integrable.
  have : -2*π ≠ 0 := by norm_num
  exact Integrable.const_mul (Integrable.comp_mul_left' pg.left this) (2:ℝ)

  -- Finally we prove that inside the integral the convergence happens poinwise.
  apply Filter.Eventually.of_forall
  intro t
  have charFuns_diff_to_zero := Tendsto.sub_const (charFuns_converge (-2*π*t)) (charFun μ (-2*π*t))
  rw [show charFun μ (-2 * π * t) - charFun μ (-2 * π * t) = 0 by simp] at charFuns_diff_to_zero
  have := Tendsto.const_mul (cexp (2 * ↑π * I * ↑x * ↑t)) charFuns_diff_to_zero
  rw [show cexp (2 * ↑π * I * ↑x * ↑t) * 0 = 0 by simp] at this
  exact this

-- In the lemma below, the application of dominated convergence needs the following elementary lemma.
lemma abs_value_min (a b : ℝ) : |a-b| = a + b - 2*(a ⊓ b) := by grind

include p_measurable p_cts f_measurable f_cts in
lemma charFun_convergence_with_densities (charFuns_converge : ∀ t:ℝ, Tendsto (fun n ↦ (charFun (ν n) t)) atTop (𝓝 (charFun μ t)))
  (exists_densities_ν : ∀ n:ℕ, withDensity volume (p n) = (ν n)) (exists_density_μ : withDensity volume f = μ)
  (charFuns_dominated : ∃ g : ℝ → ℝ, Integrable g volume ∧ (∀ (n:ℕ) (t:ℝ), ‖charFun (ν n) t‖ ≤ g t) ∧ ∀ t, ‖charFun μ t‖ ≤ g t) :
  Tendsto (fun n ↦ ∫x:ℝ, |(p n x).toReal - (f x).toReal| ∂volume) atTop (𝓝 0) := by

  -- This is a key step: we rewrite the difference so that we can apply dominated convergence to the RHS.
  have : (fun n ↦ ∫x:ℝ, |(p n x).toReal - (f x).toReal| ∂volume)
    = (fun n ↦ 2 - 2 * ∫ x:ℝ, ((p n x).toReal) ⊓ ((f x).toReal) ∂volume) := by
    ext n
    -- At fist we write 2 = 1+1 in the RHS, for some reason one needs to hold lean compilers hand here.
    have : 2 - 2 * ∫ x:ℝ, ((p n x).toReal) ⊓ ((f x).toReal) ∂volume = 1 + 1 - 2 * ∫ x:ℝ, ((p n x).toReal) ⊓ ((f x).toReal) ∂volume := by
      simp
      norm_num
    rw [this]

    -- We replace both 1's as the integrals of suitable densities here. In this part we need that p n and f are densities of probability measures.
    nth_rw 1 [← integral_of_density_eq_one (ν n) (p_measurable n) (exists_densities_ν n)]
    rw [← integral_of_density_eq_one μ f_measurable exists_density_μ]

    -- We use linearity of integral to write both sides of the equation as ∫ (something). This is probabily a bit clumsily written...
    have : ((∫ (x : ℝ), (p n x).toReal ∂volume) + ∫ (x : ℝ), (f x).toReal ∂volume) - 2 * ∫ (x : ℝ), min (p n x).toReal (f x).toReal ∂volume
      = ∫ (x : ℝ), (p n x).toReal + (f x).toReal - 2 *  min (p n x).toReal (f x).toReal ∂volume := by
      have pn_integrable := integrable_density (ν n) (p_measurable n) (exists_densities_ν n)
      have f_integrable := integrable_density μ f_measurable exists_density_μ
      have : (∫ (x : ℝ), (p n x).toReal) + ∫ (x : ℝ), (f x).toReal = ∫ (x : ℝ), (p n x).toReal + (f x).toReal := by
        have := integral_add pn_integrable f_integrable
        exact Eq.symm this
      rw [this]
      have : (∫ (x : ℝ), (p n x).toReal + (f x).toReal) - 2 * ∫ (x : ℝ), min (p n x).toReal (f x).toReal
        = (∫ (x : ℝ), (p n x).toReal + (f x).toReal) + (- 2) * ∫ (x : ℝ), min (p n x).toReal (f x).toReal := by grind
      rw [this]
      rw [← integral_const_mul (-2:ℝ) (fun x:ℝ ↦ min (p n x).toReal (f x).toReal)]
      have pn_plus_f_integrable : Integrable (fun x:ℝ ↦ (p n x).toReal + (f x).toReal) :=
        (integrable_add_iff_integrable_left' f_integrable).mpr pn_integrable
      have f_integrable' : Integrable (fun x:ℝ ↦ -2*min (p n x).toReal (f x).toReal) :=
        Integrable.const_mul (Integrable.inf pn_integrable f_integrable) (-2)
      have := integral_add pn_plus_f_integrable f_integrable'
      rw [← this]
      grind
    rw [this]

    -- At this point we are ready to reduce the claim to an application of the abs_value_min lemma.
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp
    exact abs_value_min (p n x).toReal (f x).toReal
  rw [this]

  -- Now with the correctly formulated limit, we can use dominated convergence.
  have limit_by_dominated : Tendsto (fun n ↦ 2 * ∫ x:ℝ, ((p n x).toReal) ⊓ ((f x).toReal) ∂volume) atTop (𝓝 (2:ℝ)) := by
    have : (2:ℝ)*1 =2 := (MulOneClass.mul_one 2)
    nth_rw 2 [← this]
    apply Tendsto.const_mul 2
    rw [← integral_of_density_eq_one μ f_measurable exists_density_μ]
    apply tendsto_integral_filter_of_dominated_convergence

    -- First we prove a measurability hypothesis.
    apply Filter.Eventually.of_forall
    intro n
    measurability

    -- Then we prove a bound.
    apply Filter.Eventually.of_forall
    intro n
    apply Filter.Eventually.of_forall
    intro x
    have pn_ge_0 : (p n x).toReal ≥ 0 := by exact toReal_nonneg
    have f_ge_0 : (f x).toReal ≥ 0 := by exact toReal_nonneg
    have : min (p n x).toReal (f x).toReal ≥ 0 := le_min pn_ge_0 f_ge_0
    rw [Real.norm_of_nonneg this]
    have : min (p n x).toReal (f x).toReal ≤ (f x).toReal := by exact Std.min_le_right
    exact this

    -- Now we prove the integrability claim, which is already established earlier.
    have := integrable_density μ f_measurable exists_density_μ
    exact Integrable.iff_ofReal.mpr this

    -- Finally we prove pointwise convergence of the integrand.
    apply Filter.Eventually.of_forall
    intro x
    have := charFun_pointwise_convergence_with_densities μ p_measurable p_cts f_measurable f_cts
                              charFuns_converge exists_densities_ν exists_density_μ charFuns_dominated x
    have := Tendsto.add_const ↑(f x).toReal this
    simp at this
    rw [tendsto_ofReal_iff] at this
    exact Filter.Tendsto.min_left this

  -- Now we have essentially proved the result, we just need to do some shuffling.
  have : Tendsto (fun n:ℕ ↦ (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have := Tendsto.sub this limit_by_dominated
  simp at this
  exact this

/- We will now begin to work with the convolution of μ with a Gaussian measure, which we shall call γ.
   We allow the singular case δ = 0 to avoid type issues. -/

def γ : ℝ≥0 → Measure ℝ := fun δ ↦ gaussianReal 0 δ

lemma γ_is_gaussian {δ : ℝ≥0} (hδ : δ ≠ 0) : γ δ = withDensity volume (gaussianPDF 0 δ) := gaussianReal_of_var_ne_zero 0 hδ

lemma γ_abs_cts {δ : ℝ≥0} (hδ : δ ≠ 0) : γ δ ≪ volume := gaussianReal_absolutelyContinuous 0 hδ

lemma gaussian_conv_abs_cts  {δ : ℝ≥0} (hδ : δ ≠ 0) : conv μ (γ δ) ≪ volume := by
  have : SFinite (γ δ) := by
    rw [γ]
    exact instSFiniteOfSigmaFinite
  exact conv_absolutelyContinuous (γ_abs_cts hδ)

lemma gaussian_conv_has_density {δ:ℝ≥0} (hδ : δ ≠ 0) : μ ∗ (γ δ) = withDensity volume (∂(μ ∗ (γ δ))/∂volume) := by
  rw [γ]
  have := gaussian_conv_abs_cts μ hδ
  rw [γ] at this
  have := absolutelyContinuous_iff_withDensity_rnDeriv_eq (ν := volume) (μ := μ ∗ gaussianReal 0 δ).mp this
  exact Eq.symm this

lemma gaussian_conv_charFun_integrable {δ:ℝ≥0} (hδ : δ ≠ 0) : Integrable (charFun (μ ∗ (γ δ))) volume := by
  rw [γ]
  have : charFun (μ ∗ (gaussianReal 0 δ)) = charFun (gaussianReal 0 δ) * charFun μ := by
    ext t
    rw [charFun_conv t]
    exact mul_comm' (charFun μ t) (charFun (gaussianReal 0 δ) t)
  rw [this]
  have : charFun (gaussianReal 0 δ) = (fun t:ℝ ↦ cexp (- δ * ↑t ^ 2 / 2)) := by
    ext t
    rw [charFun_gaussianReal]
    simp
    field_simp
  rw [this]
  rw [show (fun t:ℝ ↦ cexp (- δ * ↑t ^ 2 / 2)) = (fun t:ℝ ↦ (Real.exp (- δ * t^2/2):ℂ)) by ext t ; simp]

  apply Integrable.mul_bdd

  -- We now have to prove that the assumptions of Integrable.mul_bdd hold. At first we prove that exp(-δt^2/2) is integrable.
  have : Integrable (fun t ↦ Real.exp (-δ * t^2/2)) := by
    have : (fun t ↦ Real.exp (-δ * t^2/2)) = fun x ↦ √(2*π*1/δ) * gaussianPDFReal 0 (1/δ) x := by
      unfold gaussianPDFReal
      ext t
      simp
      field_simp
    rw [this]
    apply Integrable.const_mul
    exact integrable_gaussianPDFReal 0 (1/δ)
  exact Integrable.ofReal this

  -- Next we need the strong measaurability of the characteristic function:
  measurability

  -- Finally we use the fact that the characteristic function is bounded by one.
  apply Filter.Eventually.of_forall
  intro x
  exact MeasureTheory.norm_charFun_le_one (μ := μ) x


-- Next we show that for bounded Lipschitz functions, we can find a bound for ∫ f dμ - ∫ f d(μ ∗ γ δ) that is independent of μ.
lemma lipschitz_bdd_unif_approx {L : ℝ≥0} {f : ℝ → ℝ} {δ:ℝ≥0} (f_bdd : ∃ C, ∀ (x y : ℝ), dist (f x) (f y) ≤ C) (f_Lipschitz : LipschitzWith L f):
  |∫ x:ℝ, f x ∂μ - ∫ x:ℝ, f x ∂(μ ∗ (γ δ))| ≤ L * √δ := by

  unfold conv
  have f_bound_one_point : ∃ M:ℝ, ∀ x:ℝ, |f x| ≤ M := by
    obtain ⟨C,pC⟩ := f_bdd
    use C + |f 0|
    intro x
    have := pC x 0
    rw [Real.dist_eq] at this
    have triangle_consequence : |f x| ≤ |f x - f 0| + |f 0| := by grind
    exact le_trans triangle_consequence (add_le_add_left this |f 0|)
  obtain ⟨M,pM⟩ := f_bound_one_point
  have f_cts := LipschitzWith.continuous f_Lipschitz

  have sum_measurable : AEMeasurable (fun x ↦ x.1 + x.2) (μ.prod (γ δ)) := by measurability
  have integrand_stmeasurable : AEStronglyMeasurable f (map (fun x ↦ x.1 + x.2) (μ.prod (γ δ))) := by
    apply Continuous.aestronglyMeasurable
    exact LipschitzWith.continuous f_Lipschitz
  rw [integral_map sum_measurable integrand_stmeasurable]

  have integrable_f : Integrable f μ := by
    apply Integrable.of_bound
    exact Continuous.aestronglyMeasurable f_cts
    apply Filter.Eventually.of_forall
    exact pM
  have integrable_f_circ_proj : Integrable (fun x:ℝ×ℝ ↦ f x.1) (μ.prod (γ δ)) := by
    rw [γ]
    apply Integrable.of_bound
    have : Continuous (fun x:ℝ×ℝ ↦ f x.1) := by fun_prop
    exact Continuous.aestronglyMeasurable this
    apply Filter.Eventually.of_forall
    intro x
    exact pM x.1
  have integrable_f_circ_sum : Integrable (fun x:ℝ×ℝ ↦ f (x.1 + x.2)) (μ.prod (γ δ)) := by
    rw[γ]
    apply Integrable.of_bound
    have : Continuous (fun x:ℝ×ℝ ↦ f (x.1 + x.2)) := by fun_prop
    exact Continuous.aestronglyMeasurable this
    apply Filter.Eventually.of_forall
    intro x
    exact pM (x.1+x.2)

  have : ∫ x:ℝ, f x ∂μ = ∫ x:ℝ×ℝ, f x.1 ∂ μ.prod (γ δ) := by
    have : SFinite (γ δ) := by rw [γ] ; exact instSFiniteOfSigmaFinite
    rw [integral_prod_symm (fun x:ℝ×ℝ ↦ f x.1) integrable_f_circ_proj]
    have : ∫ (y : ℝ), ∫ (x : ℝ), f (x, y).1 ∂μ ∂γ δ = (∫ (x : ℝ), f x ∂μ) * ∫ (y : ℝ), (1:ℝ) ∂γ δ := by
      rw [γ]
      simp
    simp [this, show ∫ (y : ℝ), (1:ℝ) ∂γ δ = 1 by rw [γ] ; simp]

  rw [this, ← integral_sub integrable_f_circ_proj integrable_f_circ_sum]
  apply le_trans abs_integral_le_integral_abs
  have lip_bd : (fun x:ℝ×ℝ ↦ |f x.1 - f (x.1 + x.2)|) ≤ (fun x:ℝ×ℝ ↦ L * |x.2|) := by
    intro x
    simp
    have := lipschitzWith_iff_dist_le_mul.mp f_Lipschitz x.1 (x.1+x.2)
    simp[Real.dist_eq] at this
    exact this

  have proj_integrable : Integrable (fun x:ℝ×ℝ ↦ L * |x.2|) (μ.prod (γ δ)) := by
    rw[γ]
    have : AEStronglyMeasurable (fun x:ℝ×ℝ ↦ L * |x.2|) (μ.prod (gaussianReal 0 δ)) := by measurability
    apply (integrable_prod_iff' this).mpr
    constructor
    · apply Filter.Eventually.of_forall
      intro y
      simp
      apply integrable_const (μ := μ)
    · simp
      apply Integrable.const_mul
      have : Integrable id (gaussianReal 0 δ) := IsGaussian.integrable_id
      have := Integrable.abs this
      exact this
  have diff_integrable : Integrable (fun x:ℝ×ℝ ↦ |f x.1 - f (x.1+x.2)|) (μ.prod (γ δ)) := by
    apply Integrable.abs
    exact Integrable.sub' integrable_f_circ_proj integrable_f_circ_sum

  apply le_trans (integral_mono diff_integrable proj_integrable lip_bd)

  have : ∫ (x : ℝ × ℝ), ↑L * |x.2| ∂μ.prod (γ δ) = L * ∫ u:ℝ, |u| ∂(gaussianReal 0 δ) := by
    rw [γ, integral_prod_symm (μ := μ) (ν := gaussianReal 0 δ) (fun x:ℝ×ℝ ↦ (L:ℝ) * |x.2|)]
    simp
    apply integral_const_mul
    rw [← γ]
    exact proj_integrable
  rw [this]

  have abs_mem_L2 : MemLp (fun x:ℝ ↦ |x|) 2 (gaussianReal 0 δ) := by
    apply MemLp.abs
    exact IsGaussian.memLp_two_fun_id

  have var_ineq := variance_nonneg (fun x ↦ |x|) (gaussianReal 0 δ)
  rw [variance_eq_sub abs_mem_L2] at var_ineq
  have ineq := add_le_add_left var_ineq ((∫ (x : ℝ), |x| ∂gaussianReal 0 δ) ^ 2)
  simp at ineq
  have variance_formula : ∫ (x : ℝ), x ^ 2 ∂gaussianReal 0 δ = δ := by
    have : MemLp id 2 (gaussianReal 0 δ) := by exact IsGaussian.memLp_two_id
    have variance_formula_2 := variance_eq_sub this
    simp at variance_formula_2
    rw [variance_formula_2]

  rw [variance_formula, show δ = √δ ^ 2 by norm_num] at ineq

  have δ_ge_0 : (0:ℝ) ≤ √δ := Real.sqrt_nonneg ↑δ
  have int_ge_0 : 0 ≤ ∫ (x : ℝ), |x| ∂gaussianReal 0 δ := by
    apply integral_nonneg
    exact IsAbsoluteValue.abv_nonneg'

  have claim_up_to_const := (sq_le_sq₀ int_ge_0 δ_ge_0).mp ineq
  have : 0 ≤ ↑L := by exact zero_le
  exact mul_le_mul_of_nonneg_left claim_up_to_const this

-- Remove these when done.
#check tendsto_iff_forall_lipschitz_integral_tendsto
#check conv μ (γ 1)
#check conv_withDensity_eq_lconvolution
#check conv_absolutelyContinuous
#check withDensity_absolutelyContinuous
#check gaussianReal_of_var_ne_zero


#check ProbabilityTheory.gaussianPDF_def
#check gaussianPDFReal 0 1
#check MeasureTheory.conv_withDensity_eq_lconvolution
#check MeasureTheory.rnDeriv_ae_eq_condExp
#check conv_absolutelyContinuous
#check absolutelyContinuous_iff_withDensity_rnDeriv_eq
#check rnDeriv (γ 1) volume

end charFun_convergence
