import SpecialFunctionProofAgent.BesselYAnalytic

/-!
# Argument derivatives of the standard integer Bessel Y

Cauchy estimates on the order-dependent coefficients justify differentiation
of the order derivative as a locally uniformly convergent argument series.
The existing J and Y definitions are preserved throughout.
-/

noncomputable section
namespace SpecialFunctionProofAgent
open Complex Filter
open scoped Topology

private def orderCoeff (k : ℕ) (a : ℂ) : ℂ := regularizedHGFunCoeff 0 {a + 1} k

private theorem orderCoeff_differentiable (k : ℕ) : Differentiable ℂ (orderCoeff k) :=
  (differentiable_hgCoeff_order k).comp (differentiable_id.add_const 1)

private theorem orderCoeff_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, ∀ (k : ℕ) (a : ℂ), a ∈ Metric.closedBall (c : ℂ) (1 / 2) →
      ‖orderCoeff k a‖ ≤ C * 2 ^ k / k.factorial := by
  have hcont : Continuous (fun a : ℂ => (Gamma (a + 1))⁻¹) := by
    simpa only [one_div, Function.comp_def, id_eq] using
      (differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c : ℂ) (1 / 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, ?_⟩
  intro k a ha
  have hn : ‖a - (c : ℂ)‖ ≤ 1 / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
  have hr := re_le_norm (-(a - (c : ℂ)))
  simp only [neg_re, sub_re, ofReal_re, norm_neg] at hr
  have ha' : -(1 / 2 : ℝ) ≤ a.re := by linarith
  have hb : ‖(Gamma (a + 1 + k))⁻¹‖ ≤ C * 2 ^ k :=
    (norm_gamma_inv_order_shift a ha' k).trans
      (mul_le_mul_of_nonneg_right (hC a ha) (by positivity))
  simpa only [orderCoeff, BesselProofAgent.hg_coeff, norm_mul, norm_inv,
    Complex.norm_natCast, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (show 0 ≤ ((k.factorial : ℝ)⁻¹) by positivity)

private theorem orderCoeff_deriv_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, ∀ k : ℕ, ‖deriv (orderCoeff k) (c : ℂ)‖ ≤ C * 2 ^ k / k.factorial := by
  obtain ⟨C, hC⟩ := orderCoeff_bound c hc
  refine ⟨2 * C, ?_⟩
  intro k
  have heq := Complex.cderiv_eq_deriv (f := orderCoeff k) (z := (c : ℂ)) (U := Set.univ)
    isOpen_univ (orderCoeff_differentiable k).differentiableOn
    (by norm_num : (0 : ℝ) < 1 / 2) (Set.subset_univ _)
  rw [← heq]
  have h := Complex.norm_cderiv_le (f := orderCoeff k) (z := (c : ℂ))
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun a ha => hC k a (Metric.sphere_subset_closedBall ha))
  convert h using 1
  ring

private theorem differentiableAt_hg_order (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    DifferentiableAt ℂ (fun a : ℂ => regularizedHGFun 0 {a + 1} z) (c : ℂ) := by
  obtain ⟨C, hC⟩ := orderCoeff_bound c hc
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    ((Real.summable_pow_div_factorial (2 * ‖z‖)).mul_left C)
    (F := fun k a => z ^ k * orderCoeff k a)
    (U := Metric.ball (c : ℂ) (1 / 2))
    (fun k => ((differentiable_const _).mul (orderCoeff_differentiable k)).differentiableOn)
    Metric.isOpen_ball ?_
  · have heq : (fun a : ℂ => ∑' k : ℕ, z ^ k * orderCoeff k a) =
        (fun a : ℂ => regularizedHGFun 0 {a + 1} z) := by
      funext a
      exact (BesselProofAgent.hg_hasSum (a + 1) z).tsum_eq
    rw [heq] at hd
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by norm_num)))
  · intro k a ha
    rw [norm_mul, norm_pow]
    calc
      ‖z‖ ^ k * ‖orderCoeff k a‖ ≤ ‖z‖ ^ k * (C * 2 ^ k / k.factorial) :=
        mul_le_mul_of_nonneg_left (hC k a (Metric.ball_subset_closedBall ha)) (by positivity)
      _ = C * ((2 * ‖z‖) ^ k / k.factorial) := by rw [mul_pow]; ring

private theorem hasSum_orderCoeff_deriv (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    HasSum (fun k : ℕ => z ^ k * deriv (orderCoeff k) (c : ℂ))
      (deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} z) (c : ℂ)) := by
  obtain ⟨C, hC⟩ := orderCoeff_bound c hc
  have hs := Complex.hasSum_deriv_of_summable_norm
    ((Real.summable_pow_div_factorial (2 * ‖z‖)).mul_left C)
    (F := fun k a => z ^ k * orderCoeff k a)
    (U := Metric.ball (c : ℂ) (1 / 2))
    (fun k => ((differentiable_const _).mul (orderCoeff_differentiable k)).differentiableOn)
    Metric.isOpen_ball ?_ (Metric.mem_ball_self (by norm_num))
  · have heq : (fun a : ℂ => ∑' k : ℕ, z ^ k * orderCoeff k a) =
        (fun a : ℂ => regularizedHGFun 0 {a + 1} z) := by
      funext a
      exact (BesselProofAgent.hg_hasSum (a + 1) z).tsum_eq
    rw [heq] at hs
    convert hs using 1
    funext k
    exact ((orderCoeff_differentiable k (c : ℂ)).hasDerivAt.const_mul (z ^ k)).deriv.symm
  · intro k a ha
    rw [norm_mul, norm_pow]
    calc
      ‖z‖ ^ k * ‖orderCoeff k a‖ ≤ ‖z‖ ^ k * (C * 2 ^ k / k.factorial) :=
        mul_le_mul_of_nonneg_left (hC k a (Metric.ball_subset_closedBall ha)) (by positivity)
      _ = C * ((2 * ‖z‖) ^ k / k.factorial) := by rw [mul_pow]; ring

private theorem orderCoeff_deriv_step (c : ℂ) (k : ℕ) :
    (k + 1 : ℂ) * deriv (orderCoeff (k + 1)) c = deriv (orderCoeff k) (c + 1) := by
  have heq : (fun a : ℂ => (k + 1 : ℂ) * orderCoeff (k + 1) a) =
      (fun a : ℂ => orderCoeff k (a + 1)) := by
    funext a
    exact BesselProofAgent.hg_coeff_derivative (a + 1) k
  have hl := ((orderCoeff_differentiable (k + 1) c).hasDerivAt.const_mul (k + 1 : ℂ))
  have hr := ((orderCoeff_differentiable k (c + 1)).hasDerivAt.comp c
    ((hasDerivAt_id c).add_const 1))
  rw [heq] at hl
  simpa using hl.unique hr

private theorem hasDerivAt_hg_order_deriv (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    HasDerivAt (fun w : ℂ => deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} w) (c : ℂ))
      (deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} z) ((c : ℂ) + 1)) z := by
  obtain ⟨C, hC⟩ := orderCoeff_deriv_bound c hc
  let R : ℝ := ‖z‖ + 1
  let F : ℕ → ℂ → ℂ := fun k w => w ^ k * deriv (orderCoeff k) (c : ℂ)
  have hf (k : ℕ) : Differentiable ℂ (F k) :=
    (differentiable_id.pow k).mul_const _
  have hb : ∀ k w, w ∈ Metric.ball (0 : ℂ) R →
      ‖F k w‖ ≤ C * ((2 * R) ^ k / k.factorial) := by
    intro k w hw
    have hw' : ‖w‖ ≤ R := le_of_lt (by simpa using hw)
    dsimp [F]
    rw [norm_mul, norm_pow]
    calc
      ‖w‖ ^ k * ‖deriv (orderCoeff k) (c : ℂ)‖ ≤
          R ^ k * (C * 2 ^ k / k.factorial) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw' k) (hC k)
          (norm_nonneg _) (pow_nonneg (by dsimp [R]; positivity) _)
      _ = C * ((2 * R) ^ k / k.factorial) := by rw [mul_pow]; ring
  have hz : z ∈ Metric.ball (0 : ℂ) R := by simp [R]
  have hsum := ((Real.summable_pow_div_factorial (2 * R)).mul_left C)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hsum
    (fun k => (hf k).differentiableOn) Metric.isOpen_ball hb
  have hs := Complex.hasSum_deriv_of_summable_norm hsum
    (fun k => (hf k).differentiableOn) Metric.isOpen_ball hb hz
  have heq : (fun w : ℂ => ∑' k : ℕ, F k w) =
      (fun w : ℂ => deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} w) (c : ℂ)) := by
    funext w
    exact (hasSum_orderCoeff_deriv c hc w).tsum_eq
  rw [heq] at hd hs
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  have hzero : deriv (F 0) z = 0 := by simp [F]
  simp only [Finset.sum_range_one, hzero, sub_zero] at hs'
  have hshift : (fun k : ℕ => deriv (F (k + 1)) z) =
      (fun k : ℕ => z ^ k * deriv (orderCoeff k) ((c : ℂ) + 1)) := by
    funext k
    have hk := (((hasDerivAt_id z).pow (k + 1)).mul_const
      (deriv (orderCoeff (k + 1)) (c : ℂ))).deriv
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one] at hk
    dsimp [F]
    rw [hk]
    calc
      (k + 1 : ℂ) * z ^ k * deriv (orderCoeff (k + 1)) (c : ℂ) =
          z ^ k * ((k + 1 : ℂ) * deriv (orderCoeff (k + 1)) (c : ℂ)) := by ring
      _ = _ := by rw [orderCoeff_deriv_step]
  rw [hshift] at hs'
  have hv := hs'.unique (by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      hasSum_orderCoeff_deriv (c + 1) (by linarith) z)
  rw [← hv]
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt

private theorem besselJ_order_deriv_eq (c : ℝ) (hc : 0 ≤ c) (z : ℂ) (hz : z ≠ 0) :
    deriv (fun a : ℂ => Complex.besselJ a z) (c : ℂ) =
      (z / 2) ^ (c : ℂ) * log (z / 2) * regularizedHGFun 0 {(c : ℂ) + 1} (-(z / 2) ^ 2) +
      (z / 2) ^ (c : ℂ) *
        deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} (-(z / 2) ^ 2)) (c : ℂ) := by
  have hp := (hasDerivAt_id (c : ℂ)).const_cpow
    (c := z / 2) (.inl (div_ne_zero hz (by norm_num)))
  have hd := hp.mul (differentiableAt_hg_order c hc (-(z / 2) ^ 2)).hasDerivAt
  change HasDerivAt (fun a : ℂ => Complex.besselJ a z) _ (c : ℂ) at hd
  simpa only [mul_one, id_eq] using hd.deriv

private theorem hasDerivAt_besselJ_order_deriv (c : ℝ) (hc : 0 ≤ c)
    (z : ℂ) (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => deriv (fun a : ℂ => Complex.besselJ a w) (c : ℂ))
      ((1 / z) * Complex.besselJ (c : ℂ) z +
        ((c : ℂ) / z) * deriv (fun a : ℂ => Complex.besselJ a z) (c : ℂ) -
        deriv (fun a : ℂ => Complex.besselJ a z) ((c : ℂ) + 1)) z := by
  have hz0 := slitPlane_ne_zero hz
  have ht : z / 2 ∈ slitPlane := by
    rcases hz with h | h
    · left
      simpa [Complex.div_re] using (div_pos h (by norm_num : (0 : ℝ) < 2))
    · right
      simpa [Complex.div_im] using (div_ne_zero h (by norm_num : (2 : ℝ) ≠ 0))
  have hbase : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z := (hasDerivAt_id z).div_const 2
  have hp := hbase.cpow_const (c := (c : ℂ)) ht
  have hl := hbase.clog ht
  have harg := (hbase.pow 2).neg
  have hh := (BesselProofAgent.hg_hasDerivAt ((c : ℂ) + 1) (-(z / 2) ^ 2)).comp z harg
  have hq := (hasDerivAt_hg_order_deriv c hc (-(z / 2) ^ 2)).comp z harg
  have hd := ((hp.mul hl).mul hh).add (hp.mul hq)
  have hevent : (fun w : ℂ =>
      (w / 2) ^ (c : ℂ) * log (w / 2) * regularizedHGFun 0 {(c : ℂ) + 1} (-(w / 2) ^ 2) +
      (w / 2) ^ (c : ℂ) *
        deriv (fun a : ℂ => regularizedHGFun 0 {a + 1} (-(w / 2) ^ 2)) (c : ℂ))
      =ᶠ[𝓝 z] (fun w : ℂ => deriv (fun a : ℂ => Complex.besselJ a w) (c : ℂ)) := by
    filter_upwards [eventually_ne_nhds hz0] with w hw
    exact (besselJ_order_deriv_eq c hc w hw).symm
  have hd' := hd.congr_of_eventuallyEq hevent.symm
  dsimp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, Pi.mul_apply] at hd'
  convert hd' using 1
  rw [besselJ_order_deriv_eq c hc z hz0]
  have hnext := besselJ_order_deriv_eq (c + 1) (by linarith) z hz0
  simp only [ofReal_add, ofReal_one] at hnext
  rw [hnext]
  have ht0 : z / 2 ≠ 0 := slitPlane_ne_zero ht
  simp only [Complex.besselJ, cpow_add _ _ ht0, cpow_sub _ _ ht0, cpow_one,
    Nat.cast_ofNat]
  field_simp
  ring

private theorem realBesselJ_order_deriv_re (c : ℝ) (hc : 0 ≤ c) (x : ℝ) (hx : 0 < x) :
    deriv (fun a : ℝ => realBesselJ a x) c =
      (deriv (fun a : ℂ => Complex.besselJ a (x : ℂ)) (c : ℂ)).re := by
  have hp : DifferentiableAt ℂ (fun a : ℂ => ((x : ℂ) / 2) ^ a) (c : ℂ) :=
    differentiableAt_id.const_cpow (.inl (div_ne_zero
      (by exact_mod_cast ne_of_gt hx) (by norm_num)))
  have hd := hp.mul (differentiableAt_hg_order c hc (-((x : ℂ) / 2) ^ 2))
  change DifferentiableAt ℂ (fun a : ℂ => Complex.besselJ a (x : ℂ)) (c : ℂ) at hd
  exact hd.hasDerivAt.real_of_complex.deriv

/-- The order derivative of the existing J has its expected argument derivative
at every nonnegative real order and positive argument. -/
theorem hasDerivAt_realBesselJ_order_deriv_of_nonneg (c : ℝ) (hc : 0 ≤ c)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) c)
      ((1 / x) * realBesselJ c x +
        (c / x) * deriv (fun a : ℝ => realBesselJ a x) c -
        deriv (fun a : ℝ => realBesselJ a x) (c + 1)) x := by
  have hd := (hasDerivAt_besselJ_order_deriv c hc (x : ℂ)
    (Complex.ofReal_mem_slitPlane.mpr hx)).real_of_complex
  have hevent : (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) c) =ᶠ[𝓝 x]
      (fun t : ℝ => (deriv (fun a : ℂ => Complex.besselJ a (t : ℂ)) (c : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact realBesselJ_order_deriv_re c hc t ht
  have hd' := hd.congr_of_eventuallyEq hevent
  have hdiv : (1 : ℂ) / (x : ℂ) = ((1 / x : ℝ) : ℂ) := by push_cast; rfl
  have hcdiv : (c : ℂ) / (x : ℂ) = ((c / x : ℝ) : ℂ) := by push_cast; rfl
  rw [hdiv, hcdiv, sub_re, add_re, re_ofReal_mul, re_ofReal_mul] at hd'
  have hnext := realBesselJ_order_deriv_re (c + 1) (by linarith) x hx
  simp only [ofReal_add, ofReal_one] at hnext
  rw [← realBesselJ_order_deriv_re c hc x hx, ← hnext] at hd'
  exact hd'

/-- Order/argument derivative exchange at order zero on the positive real axis. -/
theorem realBesselJ_order_derivative_exchange_zero (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 0)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 0) x := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  rw [realBesselJ_order_deriv_argument_deriv 0 x hx h0 (by simpa using h1)]
  exact hasDerivAt_realBesselJ_order_deriv_of_nonneg 0 (by norm_num) x hx

/-- Order/argument derivative exchange at order one on the positive real axis. -/
theorem realBesselJ_order_derivative_exchange_one (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 1)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 1) x := by
  have h1 := differentiableAt_realBesselJ_int_order 1 x hx
  have h2 := differentiableAt_realBesselJ_int_order 2 x hx
  rw [realBesselJ_order_deriv_argument_deriv 1 x hx (by simpa using h1) (by norm_num at h2 ⊢; exact h2)]
  exact hasDerivAt_realBesselJ_order_deriv_of_nonneg 1 (by norm_num) x hx

/-- The exchange at order -1 follows from the differentiated order recurrence. -/
theorem realBesselJ_order_derivative_exchange_neg_one (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) (-1))
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) (-1)) x := by
  have hrec (t : ℝ) (ht : 0 < t) := realBesselJ_order_deriv_recurrence 0 t ht
    (by simpa using differentiableAt_realBesselJ_int_order (-1) t ht)
    (by simpa using differentiableAt_realBesselJ_int_order 0 t ht)
    (by simpa using differentiableAt_realBesselJ_int_order 1 t ht)
  have hevent : (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) (-1)) =ᶠ[𝓝 x]
      (fun t : ℝ => (2 / t) * realBesselJ 0 t - deriv (fun a : ℝ => realBesselJ a t) 1) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have hr := hrec t ht
    norm_num at hr
    linarith
  have hd := ((((hasDerivAt_const x (2 : ℝ)).div (hasDerivAt_id x) (ne_of_gt hx)).mul
    (hasDerivAt_realBesselJ 0 x hx)).sub
    (hasDerivAt_realBesselJ_order_deriv_of_nonneg 1 (by norm_num) x hx)).congr_of_eventuallyEq hevent
  have hr0 := hrec x hx
  have hr1 := realBesselJ_order_deriv_recurrence 1 x hx
    (by simpa using differentiableAt_realBesselJ_int_order 0 x hx)
    (by simpa using differentiableAt_realBesselJ_int_order 1 x hx)
    (by norm_num; exact differentiableAt_realBesselJ_int_order 2 x hx)
  have harg := realBesselJ_order_deriv_argument_deriv (-1) x hx
    (by simpa using differentiableAt_realBesselJ_int_order (-1) x hx)
    (by simpa using differentiableAt_realBesselJ_int_order 0 x hx)
  have hneg := realBesselJ_neg_int 1 x
  norm_num at hr0 hr1 harg hneg hd
  have hm : deriv (fun a : ℝ => realBesselJ a x) (-1) =
      (2 / x) * realBesselJ 0 x - deriv (fun a : ℝ => realBesselJ a x) 1 := by linarith
  have htwo : deriv (fun a : ℝ => realBesselJ a x) 2 =
      (2 / x) * realBesselJ 1 x + (2 / x) * deriv (fun a : ℝ => realBesselJ a x) 1 -
        deriv (fun a : ℝ => realBesselJ a x) 0 := by linarith
  convert hd using 1
  rw [harg, hneg, hm, htwo]
  field_simp
  ring

/-- The standard integer Y₀ has derivative -Y₁ for positive real arguments. -/
theorem hasDerivAt_besselYInt_zero (x : ℝ) (hx : 0 < x) :
    HasDerivAt (besselYInt 0) (-besselYInt 1 x) x := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  exact hasDerivAt_besselYInt_zero_of_order_derivative_exchange x hx h0 h1
    (realBesselJ_order_derivative_exchange_zero x hx)

/-- The derivative-value form of the positive-axis Y₀ identity. -/
theorem deriv_besselYInt_zero (x : ℝ) (hx : 0 < x) :
    deriv (besselYInt 0) x = -besselYInt 1 x :=
  (hasDerivAt_besselYInt_zero x hx).deriv

/-- The standard integer Y₁ has derivative Y₀-Y₁/x for positive real arguments. -/
theorem hasDerivAt_besselYInt_one (x : ℝ) (hx : 0 < x) :
    HasDerivAt (besselYInt 1) (besselYInt 0 x - besselYInt 1 x / x) x := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  exact hasDerivAt_besselYInt_one_of_order_derivative_exchange x hx h0 h1
    (realBesselJ_order_derivative_exchange_one x hx)
    (realBesselJ_order_derivative_exchange_neg_one x hx)

/-- The derivative-value form of the positive-axis Y₁ identity. -/
theorem deriv_besselYInt_one (x : ℝ) (hx : 0 < x) :
    deriv (besselYInt 1) x = besselYInt 0 x - besselYInt 1 x / x :=
  (hasDerivAt_besselYInt_one x hx).deriv

#print axioms hasDerivAt_realBesselJ_order_deriv_of_nonneg
#print axioms realBesselJ_order_derivative_exchange_zero
#print axioms realBesselJ_order_derivative_exchange_one
#print axioms realBesselJ_order_derivative_exchange_neg_one
#print axioms hasDerivAt_besselYInt_zero
#print axioms deriv_besselYInt_zero
#print axioms hasDerivAt_besselYInt_one
#print axioms deriv_besselYInt_one

end SpecialFunctionProofAgent
