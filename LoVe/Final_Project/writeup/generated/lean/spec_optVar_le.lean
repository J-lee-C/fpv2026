/-- The fused variance `P R / (P + R)` is at most both `P` and `R`. -/
theorem spec_optVar_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    optVar P R ≤ P ∧ optVar P R ≤ R
