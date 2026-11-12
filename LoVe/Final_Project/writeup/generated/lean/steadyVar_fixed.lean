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
