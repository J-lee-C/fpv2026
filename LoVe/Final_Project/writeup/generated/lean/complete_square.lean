/-- Completing the square: `postVar P R K = (P + R) (K - gain P R)² + optVar P R`. -/
theorem complete_square (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R K = (P + R) * (K - gain P R)^2 + optVar P R := by
  unfold gain optVar postVar
  have pos := denom_pos P R hP hR
  field_simp
  ring
