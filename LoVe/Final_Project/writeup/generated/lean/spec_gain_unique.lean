/-- A gain that attains the smallest update variance is the Kalman gain. -/
theorem spec_gain_unique (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R)
    (h : postVar P R K = postVar P R (gain P R)) : K = gain P R
