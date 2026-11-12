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
