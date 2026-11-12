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
