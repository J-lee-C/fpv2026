-- Core
/-- The Kalman gain gives the smallest update variance among all gains `K`. -/
theorem spec_gain_optimal (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) ≤ postVar P R K
