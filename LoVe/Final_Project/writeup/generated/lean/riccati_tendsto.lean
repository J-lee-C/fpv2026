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
