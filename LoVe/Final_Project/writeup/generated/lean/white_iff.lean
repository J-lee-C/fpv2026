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
