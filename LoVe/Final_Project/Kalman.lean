import Mathlib

/-!
# The scalar Kalman update and extensions from a switching-diffusion model

Parts 1 and 3 hold the definitions and Part 6 the final statements: these are what a human
checks. Parts 2, 4, 4b, 4c and 5 hold the proofs, which Lean checks.
-/

noncomputable section
namespace Kalman
open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Part 1: Core definitions (HUMAN-VERIFIED)
The student's scalar update, copied verbatim: the error variance `postVar` for a gain `K`,
the Kalman gain `gain`, and the smallest variance `optVar`. -/

/-- Error variance after an update with gain K (slide 5). -/
def postVar (P R K : ℝ) : ℝ :=
  (1 - K)^2 * P + K^2 * R

/-- The Kalman gain (slide 6). -/
def gain (P R : ℝ) : ℝ := P / (P + R)

/-- The smallest possible variance, f(K*) (slide 6). -/
def optVar (P R : ℝ) : ℝ := P * R / (P + R)

/-! ## Part 2: Core theorems (human-written)
The student's statements and proofs, copied verbatim from `Core.lean`; Claude Code added
the docstrings. -/

/-! ### Lemma ladder (slide 10) -/

/-- The denominator is positive: `0 < P + R`. -/
theorem denom_pos (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    0 < P + R := by
  linarith

/-- Completing the square: `postVar P R K = (P + R) (K - gain P R)² + optVar P R`. -/
theorem complete_square (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R K = (P + R) * (K - gain P R)^2 + optVar P R := by
  unfold gain optVar postVar
  have pos := denom_pos P R hP hR
  field_simp
  ring

/-- At the Kalman gain the update variance is `optVar P R`. -/
theorem postVar_gain (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) = optVar P R := by
  unfold postVar gain optVar
  field

/-! ### Main theorems -/

/-- The Kalman gain minimizes the update variance. -/
theorem gain_optimal (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) ≤ postVar P R K := by
  have comp_sq := complete_square P R K hP hR
  have pvg := postVar_gain P R hP hR
  rw [comp_sq]
  rw [pvg]
  rw [le_add_iff_nonneg_left]
  have pos := denom_pos P R hP hR
  have square_plus := sq_nonneg (K - gain P R)
  have pos_or_zero := le_of_lt pos
  apply mul_nonneg pos_or_zero square_plus

/-- The Kalman gain is the only gain with the minimum update variance. -/
theorem gain_unique (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R)
    (h : postVar P R K = postVar P R (gain P R)) : K = gain P R := by
  have pos := denom_pos P R hP hR
  have comp_sq := complete_square P R K hP hR
  have pvg := postVar_gain P R hP hR
  rw[pvg] at h
  rw[comp_sq] at h
  rw[add_eq_right] at h
  cases mul_eq_zero.mp h with
  |inl impos => linarith
  |inr solve =>
    have zero : K - gain P R = 0 := by exact eq_zero_of_pow_eq_zero solve
    apply sub_eq_zero.mp zero

/-- The optimal variance is at most `P` and at most `R`. -/
theorem optVar_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    optVar P R ≤ P ∧ optVar P R ≤ R := by
  have pos := denom_pos P R hP hR
  unfold optVar
  field_simp
  constructor
  · have R_plus_P: R≤P+R := by linarith
    exact mul_le_mul_of_nonneg_left R_plus_P hP
  · nlinarith

/-! ## Part 3: Extension definitions (HUMAN-VERIFIED)
Scalar pieces of the switching-diffusion model: the update error as a random variable, one OU
mode's prediction and Riccati recursion, innovation autocovariances, a two-state MSM, the
general filter-variance recursion with its steady state, and the basin-switching generator. -/

/-- Error after an update with gain `K`, from prediction error `e` and sighting noise `v`. -/
def updErr {Ω : Type*} (K : ℝ) (e v : Ω → ℝ) : Ω → ℝ :=
  fun ω => (1 - K) * e ω - K * v ω

/-- Prediction step for one OU mode: decay `a`, stationary (equilibrium) variance `σ2`. -/
def ouPredict (a σ2 P : ℝ) : ℝ := a ^ 2 * P + σ2 * (1 - a ^ 2)

/-- Prior variance of an OU mode under the optimal filter, started at equilibrium `σ2`. -/
def ouRiccati (a σ2 R : ℝ) : ℕ → ℝ
  | 0     => σ2
  | n + 1 => ouPredict a σ2 (optVar (ouRiccati a σ2 R n) R)

/-- Steady-state innovation autocovariance at lag `k + 1`.
Lag 1 is `a(1-K)P - aKR`; each further lag multiplies by the filter pole `a(1-K)`. -/
def innovCov (a P R K : ℝ) : ℕ → ℝ
  | 0     => a * (1 - K) * P - a * K * R
  | k + 1 => a * (1 - K) * innovCov a P R K k

/-- Transition matrix of a two-state Markov state model, switching probabilities `p`, `q`. -/
def msm (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - p, p; q, 1 - q]

/-- Innovation autocovariance at lag `n + 1` when an unmodeled switch with eigenvalue `lam`
leaks into the innovations with strength `β`; `α` is the filter pole, `c₁` the lag-1 value. -/
def switchCov (α β lam c₁ : ℝ) : ℕ → ℝ
  | 0     => c₁
  | n + 1 => α * switchCov α β lam c₁ n + β * lam ^ (n + 1)

/-- One step of the scalar filter variance: optimal update with noise `R`, then predict
with decay `a` and process noise `Q`. -/
def riccatiStep (a Q R P : ℝ) : ℝ := a ^ 2 * optVar P R + Q

/-- Prior variance after `n` steps from initial variance `P₀`. -/
def riccatiIter (a Q R P₀ : ℝ) : ℕ → ℝ
  | 0     => P₀
  | n + 1 => riccatiStep a Q R (riccatiIter a Q R P₀ n)

/-- Steady-state prior variance: the nonnegative root of `P² + (R(1-a²) - Q)P - QR = 0`. -/
def steadyVar (a Q R : ℝ) : ℝ :=
  ((Q - R * (1 - a ^ 2)) + Real.sqrt ((R * (1 - a ^ 2) - Q) ^ 2 + 4 * Q * R)) / 2

/-- Jump rate from a basin with population density `pᵢ` to one with `pⱼ`:
symmetric prefactor `κ` times `sqrt (pⱼ / pᵢ)`. -/
def jumpRate (κ pᵢ pⱼ : ℝ) : ℝ := κ * Real.sqrt (pⱼ / pᵢ)

/-- Generator of basin switching at a fixed slow state: off-diagonal entries are jump
rates, each diagonal entry is minus its row's total outflow. -/
def generator {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then -(∑ k ∈ Finset.univ.erase i, jumpRate (κ i k) (p i) (p k))
             else jumpRate (κ i j) (p i) (p j)

/-! ## Part 4: Proofs for S, O, W, H0, H
Deterministic results: sensor fusion (S), the OU variance bound (O), white innovations (W),
and the hidden switch's eigenvector (H0) and decay rate (H). -/

/-! ### S: sensor fusion -/

/-- `0 ≤ optVar P R`: a nonnegative product over a positive sum. -/
theorem optVar_nonneg (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) : 0 ≤ optVar P R :=
  div_nonneg (mul_nonneg hP hR.le) (denom_pos P R hP hR).le

/-- Fusing `R₁` then `R₂` gives `P R₁ R₂ / (P R₁ + P R₂ + R₁ R₂)`. -/
theorem optVar_optVar (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ = P * R₁ * R₂ / (P * R₁ + P * R₂ + R₁ * R₂) := by
  unfold optVar
  field_simp
  ring

/-- Fusing two sensors in either order gives the same variance. -/
theorem fusion_comm (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ = optVar (optVar P R₂) R₁ := by
  rw [optVar_optVar P R₁ R₂ hP h₁ h₂, optVar_optVar P R₂ R₁ hP h₂ h₁]
  ring

/-- Fusing a second sensor never increases the variance. -/
theorem fusion_mono (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ ≤ optVar P R₁ := by
  have hx : 0 ≤ optVar P R₁ := optVar_nonneg P R₁ hP h₁
  exact (optVar_le (optVar P R₁) R₂ hx h₂).1

/-! ### O: an OU mode stays within its equilibrium spread -/

/-- If `0 ≤ y ≤ σ2` and `a² ≤ 1`, then `0 ≤ a² y + σ2 (1 - a²) ≤ σ2`. -/
theorem ouPredict_mem (a σ2 y : ℝ) (ha : a ^ 2 ≤ 1) (hy₀ : 0 ≤ y) (hy : y ≤ σ2) :
    0 ≤ ouPredict a σ2 y ∧ ouPredict a σ2 y ≤ σ2 := by
  have ha₀ : 0 ≤ a ^ 2 := sq_nonneg a
  have hgap : 0 ≤ 1 - a ^ 2 := by linarith
  constructor
  · exact add_nonneg (mul_nonneg ha₀ hy₀) (mul_nonneg (hy₀.trans hy) hgap)
  · calc ouPredict a σ2 y = a ^ 2 * y + σ2 * (1 - a ^ 2) := rfl
      _ ≤ a ^ 2 * σ2 + σ2 * (1 - a ^ 2) := by gcongr
      _ = σ2 := by ring

/-- `0 ≤ ouRiccati n ≤ σ2` at every step `n`. -/
theorem ou_bound (a σ2 R : ℝ) (ha : a ^ 2 ≤ 1) (hσ : 0 ≤ σ2) (hR : 0 < R) (n : ℕ) :
    0 ≤ ouRiccati a σ2 R n ∧ ouRiccati a σ2 R n ≤ σ2 := by
  induction n with
  | zero => exact ⟨hσ, le_rfl⟩
  | succ n ih =>
    have hy₀ : 0 ≤ optVar (ouRiccati a σ2 R n) R := optVar_nonneg _ R ih.1 hR
    have hy : optVar (ouRiccati a σ2 R n) R ≤ σ2 := (optVar_le _ R ih.1 hR).1.trans ih.2
    exact ouPredict_mem a σ2 _ ha hy₀ hy

/-! ### W: white innovations exactly at the Kalman gain -/

/-- Closed form: `innovCov k = (a (1 - K))^k * innovCov 0`. -/
theorem innovCov_closed (a P R K : ℝ) (k : ℕ) :
    innovCov a P R K k = (a * (1 - K)) ^ k * innovCov a P R K 0 := by
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
    change a * (1 - K) * innovCov a P R K k = _
    rw [ih, pow_succ]
    ring

/-- Lag 1 measures the gain error: `innovCov 0 = a (P + R) (gain P R - K)`. -/
theorem innovCov_zero (a P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    innovCov a P R K 0 = a * (P + R) * (gain P R - K) := by
  rw [innovCov, gain]
  field_simp
  ring

/-- All lags vanish iff `K` is the Kalman gain. -/
theorem white_iff (a P R K : ℝ) (ha : a ≠ 0) (hP : 0 ≤ P) (hR : 0 < R) :
    (∀ k, innovCov a P R K k = 0) ↔ K = gain P R := by
  have hne : a * (P + R) ≠ 0 := mul_ne_zero ha (denom_pos P R hP hR).ne'
  constructor
  · intro hwhite
    have hlag1 : a * (P + R) * (gain P R - K) = 0 := by
      rw [← innovCov_zero a P R K hP hR]
      exact hwhite 0
    exact (sub_eq_zero.1 ((mul_eq_zero.1 hlag1).resolve_left hne)).symm
  · rintro rfl k
    rw [innovCov_closed, innovCov_zero a P R _ hP hR, sub_self, mul_zero, mul_zero]

/-! ### H0: the switch's eigenvector -/

/-- `(p, -q)` is an eigenvector of `msm p q` with eigenvalue `1 - p - q`. -/
theorem msm_eigen (p q : ℝ) :
    (msm p q).mulVec ![p, -q] = (1 - p - q) • ![p, -q] := by
  ext i
  fin_cases i <;> simp [msm, Matrix.mulVec, dotProduct] <;> ring

/-! ### H: the switch's decay rate dominates the innovations -/

/-- `|α| < |lam|` forces `lam ≠ 0` and `lam - α ≠ 0`. -/
theorem lam_ne (α lam : ℝ) (hlt : |α| < |lam|) : lam ≠ 0 ∧ lam - α ≠ 0 := by
  constructor
  · rintro rfl
    rw [abs_zero] at hlt
    linarith [abs_nonneg α]
  · intro h
    rw [sub_eq_zero.1 h] at hlt
    exact lt_irrefl _ hlt

/-- Closed form `switchCov n = (c₁ - B) α^n + B lam^n`, where `B = β lam / (lam - α)`. -/
theorem switchCov_closed (α β lam c₁ : ℝ) (hne : lam - α ≠ 0) (n : ℕ) :
    switchCov α β lam c₁ n
      = (c₁ - β * lam / (lam - α)) * α ^ n + β * lam / (lam - α) * lam ^ n := by
  induction n with
  | zero => simp [switchCov]
  | succ n ih =>
    change α * switchCov α β lam c₁ n + β * lam ^ (n + 1) = _
    rw [ih]
    field_simp
    ring

/-- `switchCov n / lam^n → β lam / (lam - α)`, because `(α / lam)^n → 0`. -/
theorem switchCov_div_tendsto (α β lam c₁ : ℝ) (hlt : |α| < |lam|) :
    Tendsto (fun n => switchCov α β lam c₁ n / lam ^ n) atTop
      (𝓝 (β * lam / (lam - α))) := by
  obtain ⟨hlam, hne⟩ := lam_ne α lam hlt
  have hr : |α / lam| < 1 := by rwa [abs_div, div_lt_one (abs_pos.2 hlam)]
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).const_mul
    (c₁ - β * lam / (lam - α))).add_const (β * lam / (lam - α))
  rw [mul_zero, zero_add] at hlim
  refine hlim.congr fun n => ?_
  rw [switchCov_closed α β lam c₁ hne, div_pow]
  field_simp

/-- The ratio of successive lags tends to the switch eigenvalue `lam`. -/
theorem switch_ratio (α β lam c₁ : ℝ) (hβ : β ≠ 0) (hlt : |α| < |lam|) :
    Tendsto (fun n => switchCov α β lam c₁ (n + 1) / switchCov α β lam c₁ n)
      atTop (𝓝 lam) := by
  obtain ⟨hlam, hne⟩ := lam_ne α lam hlt
  have hB : β * lam / (lam - α) ≠ 0 := div_ne_zero (mul_ne_zero hβ hlam) hne
  have hu := switchCov_div_tendsto α β lam c₁ hlt
  have hlim := ((hu.comp (tendsto_add_atTop_nat 1)).div hu hB).const_mul lam
  rw [div_self hB, mul_one] at hlim
  refine hlim.congr fun n => ?_
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp
  ring

/-! ## Part 4b: Proofs for F (the filter forgets its start and converges)
One step of the variance recursion contracts gaps by `a²`; `steadyVar` solves the fixed-point
quadratic; every run converges to it; and there the Kalman gain gives white innovations. -/

/-! ### F: two runs forget their difference -/

/-- For `x, y ≥ 0` the update shrinks gaps: `|optVar x R - optVar y R| ≤ |x - y|`. -/
theorem optVar_lipschitz (x y R : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : 0 < R) :
    |optVar x R - optVar y R| ≤ |x - y| := by
  have hxR := denom_pos x R hx hR
  have hyR := denom_pos y R hy hR
  have hgap : optVar x R - optVar y R = R ^ 2 / ((x + R) * (y + R)) * (x - y) := by
    unfold optVar
    field_simp
    ring
  have hfac₀ : 0 ≤ R ^ 2 / ((x + R) * (y + R)) := by positivity
  have hfac₁ : R ^ 2 / ((x + R) * (y + R)) ≤ 1 := by
    rw [div_le_one (mul_pos hxR hyR)]
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hR.le, mul_nonneg hy hR.le]
  rw [hgap, abs_mul, abs_of_nonneg hfac₀]
  exact mul_le_of_le_one_left (abs_nonneg _) hfac₁

/-- One filter step shrinks gaps by the factor `a²`. -/
theorem riccatiStep_lipschitz (a Q R x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : 0 < R) :
    |riccatiStep a Q R x - riccatiStep a Q R y| ≤ a ^ 2 * |x - y| := by
  have hgap : riccatiStep a Q R x - riccatiStep a Q R y
      = a ^ 2 * (optVar x R - optVar y R) := by
    unfold riccatiStep
    ring
  rw [hgap, abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_left (optVar_lipschitz x y R hx hy hR) (sq_nonneg a)

/-- Every iterate of the filter variance is nonnegative. -/
theorem riccatiIter_nonneg (a Q R P₀ : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R) (h₀ : 0 ≤ P₀)
    (n : ℕ) : 0 ≤ riccatiIter a Q R P₀ n := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact add_nonneg (mul_nonneg (sq_nonneg a) (optVar_nonneg _ R ih hR)) hQ

/-- Two runs from nonnegative starts approach each other: gap `≤ (a²)ⁿ ×` initial gap. -/
theorem riccati_contract (a Q R P₀ P₀' : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R) (h₀ : 0 ≤ P₀)
    (h₀' : 0 ≤ P₀') (n : ℕ) :
    |riccatiIter a Q R P₀ n - riccatiIter a Q R P₀' n| ≤ (a ^ 2) ^ n * |P₀ - P₀'| := by
  induction n with
  | zero => simp [riccatiIter]
  | succ n ih =>
    calc |riccatiIter a Q R P₀ (n + 1) - riccatiIter a Q R P₀' (n + 1)|
        ≤ a ^ 2 * |riccatiIter a Q R P₀ n - riccatiIter a Q R P₀' n| :=
          riccatiStep_lipschitz a Q R _ _ (riccatiIter_nonneg a Q R P₀ hQ hR h₀ n)
            (riccatiIter_nonneg a Q R P₀' hQ hR h₀' n) hR
      _ ≤ a ^ 2 * ((a ^ 2) ^ n * |P₀ - P₀'|) := by gcongr
      _ = (a ^ 2) ^ (n + 1) * |P₀ - P₀'| := by ring

/-! ### F: the steady state -/

/-- The steady state is nonnegative, because `√D ≥ |Q - R(1 - a²)|`. -/
theorem steadyVar_nonneg (a Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R) : 0 ≤ steadyVar a Q R := by
  have hD : (Q - R * (1 - a ^ 2)) ^ 2 ≤ (R * (1 - a ^ 2) - Q) ^ 2 + 4 * Q * R := by
    nlinarith [mul_nonneg hQ hR.le]
  have hroot := Real.abs_le_sqrt hD
  have hneg := neg_abs_le (Q - R * (1 - a ^ 2))
  unfold steadyVar
  linarith

/-- The steady state is a fixed point of the filter step. -/
theorem steadyVar_fixed (a Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R) :
    riccatiStep a Q R (steadyVar a Q R) = steadyVar a Q R := by
  have hpos := denom_pos _ R (steadyVar_nonneg a Q R hQ hR) hR
  have hD : 0 ≤ (R * (1 - a ^ 2) - Q) ^ 2 + 4 * Q * R := by positivity
  have hroot :
      steadyVar a Q R ^ 2 + (R * (1 - a ^ 2) - Q) * steadyVar a Q R - Q * R = 0 := by
    unfold steadyVar
    linear_combination (1 / 4 : ℝ) * Real.sq_sqrt hD
  unfold riccatiStep optVar
  field_simp
  linear_combination -hroot

/-- Started at the steady state, the filter stays there. -/
theorem riccatiIter_steady (a Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R) (n : ℕ) :
    riccatiIter a Q R (steadyVar a Q R) n = steadyVar a Q R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change riccatiStep a Q R (riccatiIter a Q R (steadyVar a Q R) n) = _
    rw [ih, steadyVar_fixed a Q R hQ hR]

/-! ### F: convergence and calibration -/

/-- From any nonnegative start the filter variance converges to the steady state. -/
theorem riccati_tendsto (a Q R : ℝ) (ha : a ^ 2 < 1) (hQ : 0 ≤ Q) (hR : 0 < R) (P₀ : ℝ)
    (h₀ : 0 ≤ P₀) : Tendsto (riccatiIter a Q R P₀) atTop (𝓝 (steadyVar a Q R)) := by
  have hP := steadyVar_nonneg a Q R hQ hR
  have hbound := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a) ha).mul_const
    |P₀ - steadyVar a Q R|
  rw [zero_mul] at hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound
  have hgap := riccati_contract a Q R P₀ _ hQ hR h₀ hP n
  rw [riccatiIter_steady a Q R hQ hR n] at hgap
  rwa [Real.norm_eq_abs]

/-- At the steady state the Kalman gain gives white innovations. -/
theorem steady_white (a Q R : ℝ) (ha0 : a ≠ 0) (hQ : 0 ≤ Q) (hR : 0 < R) (k : ℕ) :
    innovCov a (steadyVar a Q R) R (gain (steadyVar a Q R) R) k = 0 :=
  (white_iff a _ R _ ha0 (steadyVar_nonneg a Q R hQ hR) hR).2 rfl k

/-- The filter forgets its start, has a steady state, converges to it, and is calibrated. -/
theorem filter_guarantee (a Q R : ℝ) (ha : a ^ 2 < 1) (ha0 : a ≠ 0)
    (hQ : 0 ≤ Q) (hR : 0 < R) :
    (∀ P₀ P₀' : ℝ, 0 ≤ P₀ → 0 ≤ P₀' → ∀ n,
      |riccatiIter a Q R P₀ n - riccatiIter a Q R P₀' n| ≤ (a ^ 2) ^ n * |P₀ - P₀'|) ∧
    (0 ≤ steadyVar a Q R ∧ riccatiStep a Q R (steadyVar a Q R) = steadyVar a Q R) ∧
    (∀ P₀ : ℝ, 0 ≤ P₀ → Tendsto (riccatiIter a Q R P₀) atTop (𝓝 (steadyVar a Q R))) ∧
    (∀ k, innovCov a (steadyVar a Q R) R (gain (steadyVar a Q R) R) k = 0) :=
  ⟨fun P₀ P₀' h₀ h₀' n => riccati_contract a Q R P₀ P₀' hQ hR h₀ h₀' n,
    ⟨steadyVar_nonneg a Q R hQ hR, steadyVar_fixed a Q R hQ hR⟩,
    fun P₀ h₀ => riccati_tendsto a Q R ha hQ hR P₀ h₀, steady_white a Q R ha0 hQ hR⟩

/-! ## Part 4c: Proofs for M (the switching model keeps its equilibrium)
The square-root jump rule satisfies detailed balance (M1), so the target populations are
stationary for the basin-switching generator (M2). -/

/-! ### M: detailed balance and stationary populations -/

/-- Detailed balance of the square-root rule: `pᵢ · rate(i → j) = pⱼ · rate(j → i)`. -/
theorem detailed_balance (κ pᵢ pⱼ : ℝ) (hi : 0 < pᵢ) (hj : 0 < pⱼ) :
    pᵢ * jumpRate κ pᵢ pⱼ = pⱼ * jumpRate κ pⱼ pᵢ := by
  unfold jumpRate
  rw [Real.sqrt_div hj.le, Real.sqrt_div hi.le]
  calc pᵢ * (κ * (√pⱼ / √pᵢ)) = κ * (pᵢ / √pᵢ) * √pⱼ := by ring
    _ = κ * (pⱼ / √pⱼ) * √pᵢ := by rw [Real.div_sqrt, Real.div_sqrt]; ring
    _ = pⱼ * (κ * (√pᵢ / √pⱼ)) := by ring

/-- With symmetric prefactors the target populations are stationary: `pᵀ L = 0`. -/
theorem populations_stationary {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hκ : ∀ i j, κ i j = κ j i) (hp : ∀ i, 0 < p i) :
    Matrix.vecMul p (generator κ p) = 0 := by
  ext j
  have hflow : ∀ i ∈ Finset.univ.erase j,
      p i * generator κ p i j = p j * jumpRate (κ j i) (p j) (p i) := by
    intro i hi
    simp only [generator, if_neg (Finset.ne_of_mem_erase hi), hκ i j]
    exact detailed_balance _ _ _ (hp i) (hp j)
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Finset.sum_congr rfl hflow,
    ← Finset.mul_sum]
  dsimp only [generator]
  rw [if_pos rfl]
  ring

/-! ## Part 5: Proofs for A, D (probability)
Random-variable results: the update variance formula (A), how an omitted coordinate
inflates the innovation variance (D), and the exact size of that inflation (F5). -/

/-! ### A: the variance formula from random variables -/

/-- `updErr K e v = (1 - K) • e + (-K) • v`. -/
theorem updErr_eq {Ω : Type*} (K : ℝ) (e v : Ω → ℝ) :
    updErr K e v = (1 - K) • e + (-K) • v := by
  funext ω
  simp only [updErr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `Var((1 - K) e - K v) = (1 - K)² Var e + K² Var v` for independent `e`, `v` in `L²`. -/
theorem variance_update {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (K : ℝ) :
    variance (updErr K e v) μ = postVar (variance e μ) (variance v μ) K := by
  have hind' : IndepFun ((1 - K) • e) ((-K) • v) μ :=
    hind.comp (measurable_const_mul (1 - K)) (measurable_const_mul (-K))
  rw [updErr_eq, hind'.variance_add (he.const_smul (1 - K)) (hv.const_smul (-K)),
    variance_smul, variance_smul, postVar]
  ring

/-- The gain built from the true variances minimizes the variance of the update error. -/
theorem variance_update_optimal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (hR : 0 < variance v μ) (K : ℝ) :
    variance (updErr (gain (variance e μ) (variance v μ)) e v) μ
      ≤ variance (updErr K e v) μ := by
  rw [variance_update he hv hind, variance_update he hv hind]
  exact gain_optimal _ _ K (variance_nonneg e μ) hR

/-! ### D: an omitted coordinate inflates the innovation variance -/

/-- `Var(e + v + h) = (Var e + Var v) + Var h` when `e ⟂ v` and `e + v ⟂ h`. -/
theorem innov_excess {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ) :
    variance (e + v + h) μ = (variance e μ + variance v μ) + variance h μ := by
  rw [hind.variance_add (he.add hv) hh, hev.variance_add he hv]

/-- The innovation variance over its predicted value `S = Var e + Var v` exceeds `1`. -/
theorem innov_excess_ratio {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) (hτ : 0 < variance h μ) :
    1 < variance (e + v + h) μ / (variance e μ + variance v μ) := by
  rw [innov_excess he hv hh hev hind, one_lt_div hS]
  linarith

/-! ### F5: the exact detection margin -/

/-- Exact detection margin: `Var(e + v + h) / S = 1 + Var h / S`. -/
theorem detection_margin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) :
    variance (e + v + h) μ / (variance e μ + variance v μ)
      = 1 + variance h μ / (variance e μ + variance v μ) := by
  rw [innov_excess he hv hh hev hind, add_div, div_self hS.ne']

/-! ## Part 6: Summary of verified results (HUMAN-VERIFIED)
Every result in its final form; each proof is one line citing a lemma from an earlier Part.
The `#print axioms` lines after `end Kalman` list what each result depends on. -/

-- Core
/-- The Kalman gain gives the smallest update variance among all gains `K`. -/
theorem spec_gain_optimal (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) ≤ postVar P R K :=
  gain_optimal P R K hP hR

/-- A gain that attains the smallest update variance is the Kalman gain. -/
theorem spec_gain_unique (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R)
    (h : postVar P R K = postVar P R (gain P R)) : K = gain P R :=
  gain_unique P R K hP hR h

/-- The fused variance `P R / (P + R)` is at most both `P` and `R`. -/
theorem spec_optVar_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    optVar P R ≤ P ∧ optVar P R ≤ R :=
  optVar_le P R hP hR

-- S: sensor fusion (each coordinate family is a sensor)
/-- Fusing sensors with noise `R₁` and `R₂` gives the same variance in either order. -/
theorem spec_fusion_comm (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ = optVar (optVar P R₂) R₁ :=
  fusion_comm P R₁ R₂ hP h₁ h₂

/-- Fusing a second sensor never increases the variance. -/
theorem spec_fusion_mono (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ ≤ optVar P R₁ :=
  fusion_mono P R₁ R₂ hP h₁ h₂

-- O: an OU mode is never tracked worse than its equilibrium spread
/-- For `a² ≤ 1`, the OU prior variance stays in `[0, σ2]` at every step `n`. -/
theorem spec_ou_bound (a σ2 R : ℝ) (ha : a ^ 2 ≤ 1) (hσ : 0 ≤ σ2) (hR : 0 < R) (n : ℕ) :
    0 ≤ ouRiccati a σ2 R n ∧ ouRiccati a σ2 R n ≤ σ2 :=
  ou_bound a σ2 R ha hσ hR n

-- A: the variance formula from random variables
/-- For independent `e`, `v` in `L²`: `Var((1 - K) e - K v) = postVar (Var e) (Var v) K`. -/
theorem spec_variance_update {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (K : ℝ) :
    variance (updErr K e v) μ = postVar (variance e μ) (variance v μ) K :=
  variance_update he hv hind K

/-- If `Var v > 0`, the gain `Var e / (Var e + Var v)` minimizes the update error's variance. -/
theorem spec_variance_update_optimal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (hR : 0 < variance v μ) (K : ℝ) :
    variance (updErr (gain (variance e μ) (variance v μ)) e v) μ
      ≤ variance (updErr K e v) μ :=
  variance_update_optimal he hv hind hR K

-- D: an omitted coordinate inflates the innovation variance (the 4x diagnostic)
/-- With `e ⟂ v` and `e + v ⟂ h`: `Var(e + v + h) = (Var e + Var v) + Var h`. -/
theorem spec_innov_excess {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ) :
    variance (e + v + h) μ = (variance e μ + variance v μ) + variance h μ :=
  innov_excess he hv hh hev hind

/-- If also `S = Var e + Var v > 0` and `Var h > 0`, then `Var(e + v + h) / S > 1`. -/
theorem spec_innov_excess_ratio {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) (hτ : 0 < variance h μ) :
    1 < variance (e + v + h) μ / (variance e μ + variance v μ) :=
  innov_excess_ratio he hv hh hev hind hS hτ

-- W: white innovations exactly at the Kalman gain
/-- For `a ≠ 0`: every innovation autocovariance vanishes iff `K = P / (P + R)`. -/
theorem spec_white_iff (a P R K : ℝ) (ha : a ≠ 0) (hP : 0 ≤ P) (hR : 0 < R) :
    (∀ k, innovCov a P R K k = 0) ↔ K = gain P R :=
  white_iff a P R K ha hP hR

-- H0, H (stretch): the hidden switch's fingerprint
/-- `(p, -q)` is an eigenvector of the MSM transition matrix with eigenvalue `1 - p - q`. -/
theorem spec_msm_eigen (p q : ℝ) :
    (msm p q).mulVec ![p, -q] = (1 - p - q) • ![p, -q] :=
  msm_eigen p q

/-- If `β ≠ 0` and `|α| < |lam|`, the ratio of successive lags tends to `lam`. -/
theorem spec_switch_ratio (α β lam c₁ : ℝ) (hβ : β ≠ 0) (hlt : |α| < |lam|) :
    Tendsto (fun n => switchCov α β lam c₁ (n + 1) / switchCov α β lam c₁ n)
      atTop (𝓝 lam) :=
  switch_ratio α β lam c₁ hβ hlt

-- M1: the square-root rule satisfies detailed balance
/-- For positive populations, `pᵢ · rate(i → j) = pⱼ · rate(j → i)`. -/
theorem spec_detailed_balance (κ pᵢ pⱼ : ℝ) (hi : 0 < pᵢ) (hj : 0 < pⱼ) :
    pᵢ * jumpRate κ pᵢ pⱼ = pⱼ * jumpRate κ pⱼ pᵢ :=
  detailed_balance κ pᵢ pⱼ hi hj

-- M2: the target populations are stationary for the switching generator
/-- With symmetric `κ` and positive `p`, the populations satisfy `pᵀ L = 0`. -/
theorem spec_populations_stationary {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hκ : ∀ i j, κ i j = κ j i) (hp : ∀ i, 0 < p i) :
    Matrix.vecMul p (generator κ p) = 0 :=
  populations_stationary κ p hκ hp

-- F: the filter forgets its start, converges, and is calibrated at steady state
/-- For `a² < 1`: gaps shrink like `(a²)ⁿ`; `steadyVar` is the fixed point, limit, and white. -/
theorem spec_filter_guarantee (a Q R : ℝ) (ha : a ^ 2 < 1) (ha0 : a ≠ 0)
    (hQ : 0 ≤ Q) (hR : 0 < R) :
    (∀ P₀ P₀' : ℝ, 0 ≤ P₀ → 0 ≤ P₀' → ∀ n,
      |riccatiIter a Q R P₀ n - riccatiIter a Q R P₀' n| ≤ (a ^ 2) ^ n * |P₀ - P₀'|) ∧
    (0 ≤ steadyVar a Q R ∧ riccatiStep a Q R (steadyVar a Q R) = steadyVar a Q R) ∧
    (∀ P₀ : ℝ, 0 ≤ P₀ → Tendsto (riccatiIter a Q R P₀) atTop (𝓝 (steadyVar a Q R))) ∧
    (∀ k, innovCov a (steadyVar a Q R) R (gain (steadyVar a Q R) R) k = 0) :=
  filter_guarantee a Q R ha ha0 hQ hR

-- F5: detection margin (exact form of the innovation-variance ratio)
/-- If `S = Var e + Var v > 0`, then `Var(e + v + h) / S = 1 + Var h / S`. -/
theorem spec_detection_margin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) :
    variance (e + v + h) μ / (variance e μ + variance v μ)
      = 1 + variance h μ / (variance e μ + variance v μ) :=
  detection_margin he hv hh hev hind hS

end Kalman

#print axioms Kalman.spec_gain_optimal
#print axioms Kalman.spec_gain_unique
#print axioms Kalman.spec_optVar_le
#print axioms Kalman.spec_fusion_comm
#print axioms Kalman.spec_fusion_mono
#print axioms Kalman.spec_ou_bound
#print axioms Kalman.spec_variance_update
#print axioms Kalman.spec_variance_update_optimal
#print axioms Kalman.spec_innov_excess
#print axioms Kalman.spec_innov_excess_ratio
#print axioms Kalman.spec_white_iff
#print axioms Kalman.spec_msm_eigen
#print axioms Kalman.spec_switch_ratio
#print axioms Kalman.spec_detailed_balance
#print axioms Kalman.spec_populations_stationary
#print axioms Kalman.spec_filter_guarantee
#print axioms Kalman.spec_detection_margin
