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
