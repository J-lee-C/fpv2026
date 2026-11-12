-- W: white innovations exactly at the Kalman gain
/-- For `a ≠ 0`: every innovation autocovariance vanishes iff `K = P / (P + R)`. -/
theorem spec_white_iff (a P R K : ℝ) (ha : a ≠ 0) (hP : 0 ≤ P) (hR : 0 < R) :
    (∀ k, innovCov a P R K k = 0) ↔ K = gain P R
