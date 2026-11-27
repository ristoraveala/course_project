import Mathlib
import CourseProject.CharFun.Basic

open NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators Topology Filter Complex Finset
open Measure
open scoped Real

/- In this file we prove a key step in the proof of CLT: the characteristic function of (1/√(n*Var[X 1; ℙ]) * ∑ (X k - ℙ[X k]))
   tends pointwise to the characteristic function of gaussianreal 0 1, that is cexp (-t^2/2). -/

lemma indep_sum_charFun {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : ℕ → Ω → ℝ}
  (measurable : ∀ (j:ℕ), AEMeasurable (Y j)) (indep : iIndepFun Y ℙ) (n : ℕ) : charFun (map (fun ω ↦ ∑ k : Icc 1 n, Y k ω) ℙ) = ∏ k : Icc 1 n, charFun (map (Y k) ℙ) := by
  have measurable' : ∀ j : Icc 1 n,  AEMeasurable (Y j) := by intro j ; exact measurable j
  have indep' : iIndepFun (fun i:Icc 1 n ↦ Y i) ℙ := iIndepFun_iff_finset.mp indep (Icc 1 n)
  exact iIndepFun.charFun_map_fun_sum_eq_prod measurable' indep'

lemma iid_sum_charFun {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : ℕ → Ω → ℝ}
(measurable : ∀ (j:ℕ), AEMeasurable (Y j)) (indep : iIndepFun Y ℙ) (indep_distrib : ∀ i j : ℕ,  IdentDistrib (Y i) (Y j) ℙ ℙ) (n:ℕ) :
charFun (map (fun ω ↦ ∑ k : Icc 1 n, Y k ω) ℙ) = (charFun (map (Y 1) ℙ))^n := by
  rw [indep_sum_charFun measurable indep n]
  have : (fun k : Finset.Icc 1 n ↦ charFun (map (Y k) ℙ)) = (fun k : Finset.Icc 1 n ↦ charFun (map (Y 1) ℙ)) := by
    ext k
    rw [show map (Y k) ℙ = map (Y 1) ℙ by exact (indep_distrib k 1).map_eq]
  rw [this]
  simp

private lemma sub_mean_integrable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : Ω → ℝ}
(measurable : Measurable Y) (snd_moment : Integrable (fun x:ℝ ↦ |x|^2) (map Y ℙ)) :
Integrable (fun x:ℝ ↦ |x|^2) (map (fun ω ↦ Y ω - ℙ[Y]) ℙ) := by
    have : (fun ω ↦ Y ω - ℙ[Y]) = (fun x:ℝ ↦ x - ℙ[Y]) ∘ Y := by
      ext ω
      simp
    rw [this]
    set e := (fun x:ℝ ↦ x-ℙ[Y]) with he
    have e_meas : AEMeasurable e (map Y ℙ) := by measurability
    have fun_meas : AEStronglyMeasurable (fun x:ℝ ↦ |x|^2) (map e (map Y ℙ)) := by measurability
    have : (map ((fun x ↦ x - ∫ (ω : Ω), Y ω) ∘ Y) ℙ) = (map e (map Y ℙ)) := by
      refine Eq.symm (Measure.map_map ?_ ?_)
      measurability
      exact measurable
    rw [this]
    apply (integrable_map_measure fun_meas e_meas).mpr
    rw [show (fun x ↦ |x| ^ 2) ∘ e = (fun x ↦ |x - ℙ[Y]|^2) by ext x; simp [he]]
    have ineq : ∀ᵐ (x : ℝ) ∂(map Y ℙ), ‖|x - ℙ[Y]| ^ 2‖ ≤ ‖2*|x|^2 + 2*(ℙ[Y])^2‖ := by
      apply Filter.Eventually.of_forall
      intro x
      simp
      have : 2 * x ^ 2 + 2 * (∫ (x : Ω), Y x) ^ 2 ≤ |2 * x ^ 2 + 2 * (∫ (x : Ω), Y x) ^ 2| := by apply le_abs_self
      apply le_trans _ this
      have := add_sq_le (a := x) (b := -ℙ[Y])
      simp at this
      rw [show x + -∫ (x : Ω), Y x = x - ℙ[Y] by grind,
          show 2 * (x ^ 2 + (∫ (x : Ω), Y x) ^ 2) = 2 * x^2 + 2*(ℙ[Y])^2 by grind] at this
      exact this
    have add_sum_integrable : Integrable (fun x:ℝ ↦ 2*|x|^2 + 2*(ℙ[Y])^2) (map Y ℙ) := by
      apply Integrable.add
      apply Integrable.const_mul
      exact snd_moment
      exact integrable_const (2 * (∫ (x : Ω), Y x) ^ 2)
    have : AEStronglyMeasurable (fun x:ℝ ↦ |x - ℙ[Y]|^2) (map Y ℙ) := by measurability
    exact Integrable.mono add_sum_integrable this ineq

private lemma sub_mean_integral_zero {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : Ω → ℝ}
(measurable : Measurable Y) (snd_moment : Integrable (fun x:ℝ ↦ |x|^2) (map Y ℙ)) :
∫ x:ℝ, x ∂Measure.map (fun ω ↦ Y ω - ℙ[Y]) ℙ = 0 := by
  have : ∫ x:ℝ, x ∂Measure.map (fun ω ↦ Y ω - ℙ[Y]) ℙ = ∫ ω:Ω, Y ω - ℙ[Y] ∂ℙ := by
    exact integral_map (by measurability) (by measurability)
  rw [this]
  have Y_int : Integrable Y ℙ := by
    have e_meas : AEMeasurable Y ℙ := Measurable.aemeasurable measurable
    have fun_meas : AEStronglyMeasurable id (map Y ℙ) := aestronglyMeasurable_id
    rw [show Y = id ∘ Y by simp]
    apply (integrable_map_measure fun_meas e_meas).mp
    have ineq : ∀ᵐ (x : ℝ) ∂(map Y ℙ), ‖x‖ ≤ ‖1+|x|^2‖ := by
      apply Filter.Eventually.of_forall
      intro x
      simp
      apply le_trans _ (le_abs_self (1 + x ^ 2))
      by_cases hx : |x| ≤ 1
      · apply le_trans hx
        simp
        exact sq_nonneg x
      · push Not at hx
        have hx' : 1 ≤ |x| := le_of_lt hx
        have : |x| ≤ x^2 := by
          have := mul_le_mul_of_nonneg_right hx' (abs_nonneg x)
          simp [Eq.symm (pow_two x)] at this
          exact this
        apply le_trans this
        simp
    have dom_integrable : Integrable (fun x:ℝ ↦ 1+|x|^2) (map Y ℙ) := by
      apply Integrable.add
      exact integrable_const 1
      exact snd_moment
    exact Integrable.mono dom_integrable aestronglyMeasurable_id ineq
  have const_int : Integrable (fun ω:Ω ↦ ℙ[Y]) ℙ := integrable_const (ℙ[Y])
  rw [integral_sub Y_int const_int]
  simp

lemma iid_sum_taylor_product {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : ℕ → Ω → ℝ}
(measurable : ∀ (j:ℕ), Measurable (Y j)) (indep : iIndepFun Y ℙ) (ident_distrib : ∀ i j : ℕ,  IdentDistrib (Y i) (Y j) ℙ ℙ)
(snd_moment : Integrable (fun x:ℝ ↦ |x|^2) (map (Y 1) ℙ)):
∃ ε : ℝ → ℂ, ∀ n: ℕ, ∀ c:ℝ, Continuous ε ∧ ε 0 = 0
∧ charFun (map (fun ω ↦ c * ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ ) = (fun t:ℝ ↦ ((1 - (1/2) * c^2 * (∫ x:ℝ, x^2 ∂(map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ)) * t^2 + t^2 * c^2 * ε (t * c)) ^ n :ℂ)) := by
  have : Integrable (fun x:ℝ ↦ |x|^2) (map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ) := sub_mean_integrable (measurable 1) snd_moment
  obtain ⟨ε,pε⟩ := snd_taylor_charFun (map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ) this
  use ε
  intro n c
  constructor
  · exact pε.left
  · constructor
    · exact pε.right.left
    · ext t
      have : charFun (map (fun ω ↦ c * ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ) t = charFun (map (fun ω ↦ ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ) (c*t) := by
        have scalar_multiple_formula := congr_fun (charFun_transformation (map (fun ω ↦ ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ) c 0) t
        have : map (fun x ↦ c * x + 0) (map (fun ω ↦ ∑ k:Icc 1 n, (Y (↑k) ω - ∫ (x : Ω), Y 1 x)) ℙ) = map (fun ω ↦ c * ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ := by
          have : map (fun x ↦ c * x + 0) (map (fun ω ↦ ∑ k:Icc 1 n, (Y (↑k) ω - ∫ (x : Ω), Y 1 x)) ℙ) = map ((fun x ↦ c*x+0) ∘ (fun ω ↦ ∑ k:Icc 1 n, (Y (↑k) ω - ∫ (x : Ω), Y 1 x))) ℙ := by
            apply Measure.map_map (by measurability) (by measurability)
          rw [this]
          apply Measure.map_congr
          apply Filter.Eventually.of_forall
          intro ω
          simp
        rw [this] at scalar_multiple_formula
        simp ; simp at scalar_multiple_formula
        exact scalar_multiple_formula
      rw [this]
      have indep_shifted : iIndepFun (fun k:ℕ ↦ (fun ω ↦ Y k ω - ℙ[Y 1])) := by
        have indep_shift_goal := iIndepFun.comp indep (fun k ↦ (fun x:ℝ ↦ x - ℙ[Y 1])) (by measurability)
        rw [show (fun k:ℕ ↦ (fun x ↦ x - ∫ (ω : Ω), Y 1 ω) ∘ Y k) = (fun k:ℕ ↦ (fun ω ↦ Y k ω - ℙ[Y 1])) by ext k; simp] at indep_shift_goal
        exact indep_shift_goal
      have ident_distrib_shift : ∀ i j : ℕ,  IdentDistrib (fun ω ↦ Y i ω - ℙ[Y 1]) (fun ω ↦ Y j ω - ℙ[Y 1]) ℙ ℙ := by
        intro i j
        exact IdentDistrib.sub_const (ident_distrib i j) (∫ (ω : Ω), Y 1 ω)
      have : ∀ (j : ℕ), AEMeasurable (fun ω ↦ Y j ω - ℙ[Y 1]) ℙ := by measurability
      rw [congr_fun (iid_sum_charFun this indep_shifted ident_distrib_shift n) (c*t),
          show (charFun (map (fun ω ↦ Y 1 ω - ∫ (x : Ω), Y 1 x) ℙ) ^ n) (c * t) = (charFun (map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ) (c*t) ) ^ n by simp,
          congr_fun pε.right.right (c*t)]
      apply congrArg (fun x ↦ x^n)
      set v := ∫ (x : ℝ), x ^ 2 ∂Measure.map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ with hv
      have : ∫ x:ℝ, x ∂Measure.map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ = 0 := sub_mean_integral_zero (measurable 1) snd_moment
      simp [this]
      field_simp

private lemma limit_claim (t:ℝ) (v:ℝ) (ε:ℝ → ℂ) (ε_cont : Continuous ε) (ε_zero : ε 0 = 0) :
  Tendsto (fun n:ℕ ↦ (t:ℂ) ^ 2 * (v:ℂ)⁻¹ * ε (t * √v⁻¹ * (1 / √(n+1)))) atTop (𝓝 0) := by
  rw [show (fun n:ℕ ↦ (t:ℂ) ^ 2 * (v:ℂ)⁻¹ * ε (t * √v⁻¹ * (1 / √(n+1)))) = (fun n:ℕ ↦ ((t:ℂ) ^ 2 * (v:ℂ)⁻¹) • ε (t * √v⁻¹ * (1 / √(n+1)))) by simp,
      show (0:ℂ) = ((t:ℂ) ^ 2 * (v:ℂ)⁻¹) • 0 by simp]
  apply Tendsto.const_smul
  have : (fun n:ℕ ↦ ε (t * √v⁻¹ * (1 / √(n + 1)))) = ε ∘ (fun n:ℕ ↦ t * √v⁻¹ * (1 / √(n + 1))) := by
    simp
    grind
  rw [this]
  have : Tendsto ε (𝓝 0) (𝓝 0) := by
    apply Continuous.tendsto' ε_cont 0 0
    exact ε_zero
  apply Tendsto.comp this
  rw [show (fun n:ℕ ↦ t * √v⁻¹ * (1 / √(↑n + 1))) = (fun n:ℕ ↦ (t * √v⁻¹) • (1 / √(↑n + 1))) by simp,
      show (0:ℝ) = (t * √v⁻¹) • 0 by simp]
  apply Tendsto.const_smul
  rw [show (fun n:ℕ ↦ 1 / √(n + 1)) = (fun r:ℝ ↦ r⁻¹) ∘ (fun n:ℕ ↦ √(n + 1)) by ext n ; simp]
  have : Tendsto (fun n:ℕ ↦ √(n + 1)) atTop atTop := by
    rw [show (fun n:ℕ ↦ √(n + 1)) = Real.sqrt ∘ (fun n:ℕ ↦ (n+1)) by ext n ; simp]
    apply Tendsto.comp Real.tendsto_sqrt_atTop
    apply Tendsto.atTop_add_nonneg
    exact tendsto_natCast_atTop_atTop
    simp
  apply Tendsto.comp _ this
  exact tendsto_inv_atTop_zero

-- For some reason this needed a bit more work
private lemma coercion_formula (v:ℝ) (n:ℕ) (v_ge_zero : v ≥ 0) : (((√v:ℂ))⁻¹ * (√(n:ℝ):ℂ)⁻¹) ^ 2 = (v⁻¹:ℂ) * (n:ℂ)⁻¹ := by
  field_simp
  have : (√v:ℂ) ^ 2 = (v:ℂ) := by
    rw [show (√v:ℂ) ^ 2 = ((√v:ℝ)^2:ℝ) by simp, Real.sq_sqrt v_ge_zero]
  rw [this]
  have : (√(n:ℝ):ℂ)^ 2 = (n:ℂ) := by
    have : (√(n:ℝ):ℂ) ^ 2 = ((√n:ℝ)^2:ℝ) := Eq.symm (Complex.ofReal_pow (√↑n) 2)
    rw [this]
    have : (n:ℝ) ≥ 0 := Nat.cast_nonneg' n
    simp [Real.sq_sqrt this]
  rw [this]

-- This lemma is what we need in the proof of CLT
lemma iid_sum_to_cexp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {Y : ℕ → Ω → ℝ}
(measurable : ∀ (j:ℕ), Measurable (Y j)) (indep : iIndepFun Y ℙ) (ident_distrib : ∀ i j : ℕ,  IdentDistrib (Y i) (Y j) ℙ ℙ)
(snd_moment : Integrable (fun x:ℝ ↦ |x|^2) (map (Y 1) ℙ)) (variance_nonzero : ∫(x:ℝ) , |x|^2 ∂(Measure.map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ) ≠ 0):
∀ t:ℝ , Tendsto (fun n:ℕ ↦ (charFun (map (fun ω ↦ (1/√(n*∫(x:ℝ), |x|^2 ∂(map (fun ω ↦ Y 1 ω - ℙ[Y 1]) ℙ))) * ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ ) t)) atTop (𝓝 (cexp (-t^2/2))) := by
  intro t
  set v := ∫(x:ℝ) , |x|^2 ∂(map (fun ω ↦ Y 1 ω - ∫ ω, Y 1 ω ∂ℙ) ℙ) with hv
  have hv' : v = ∫(x:ℝ) , x^2 ∂(map (fun ω ↦ Y 1 ω - ∫ ω, Y 1 ω ∂ℙ) ℙ) := by
    rw [hv]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    grind
  have v_ne_zero : v ≠ 0 := by
    rw [hv]
    exact variance_nonzero
  have v_ne_zero : (v:ℂ) ≠ (0:ℂ) := ofReal_ne_zero.mpr variance_nonzero
  have v_ge_zero : v ≥ 0 := by
    rw [hv]
    apply integral_nonneg
    intro x
    simp
    exact sq_nonneg x
  obtain ⟨ε,pε⟩ := iid_sum_taylor_product measurable indep ident_distrib snd_moment
  have approx_formula : (fun n:ℕ ↦ (charFun (map (fun ω ↦ (1/√(n*v)) * ∑ k : Icc 1 n , (Y k ω - ℙ[Y 1])) ℙ ) t))
        = (fun n:ℕ ↦ (1 - (1/n) * (1/2) * t^2 + t^2 * (1/v) * (1/n) * ε (t * (1/√v) * (1/√n)))^n) := by
    ext n
    have formula := (pε n (1/√(n*v))).right.right
    rw [formula]
    apply congrArg (fun x ↦ x^n)
    rw [← hv']
    simp [coercion_formula v n v_ge_zero]
    grind
  rw [approx_formula]
  set g : ℕ → ℂ := fun n ↦ (- 1 / n * (1 / 2) * t ^ 2 + t ^ 2 * (1 / v) * (1 / n) * ε (t * (1 / √v) * (1 / √n))) with hg
  have : (fun n:ℕ ↦ (1 - 1 / n * (1 / 2) * t ^ 2 + t ^ 2 * (1 / ↑v) * (1 / ↑n) * ε (t * (1 / √v) * (1 / √n))) ^ n) = (fun n:ℕ ↦ (1 + g n)^n) := by
    ext n
    apply congrArg (fun x ↦ x^n)
    grind
  rw [this]
  have : Tendsto (fun (n:ℕ) ↦ n * g n) atTop (𝓝 (-t^2/2)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have : (fun (n:ℕ) ↦ ((n+1):ℕ) * g (n+1)) = (fun n:ℕ ↦ - t ^ 2/2 + (t:ℂ) ^ 2 * (v:ℂ)⁻¹ * ε (t * (√v)⁻¹ * (√(n+1))⁻¹)) := by
      ext n
      rw [hg]
      simp
      field_simp
    rw [this]
    have := limit_claim t v ε (pε 0 0).left (pε 0 0).right.left
    have := Tendsto.const_add (-(t:ℂ)^2/2) this
    simp at this
    exact this
  exact Complex.tendsto_one_add_pow_exp_of_tendsto this
