/-- Fusing a second sensor never increases the variance. -/
theorem spec_fusion_mono (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ ≤ optVar P R₁
