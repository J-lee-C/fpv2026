-- S: sensor fusion (each coordinate family is a sensor)
/-- Fusing sensors with noise `R₁` and `R₂` gives the same variance in either order. -/
theorem spec_fusion_comm (P R₁ R₂ : ℝ) (hP : 0 ≤ P) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    optVar (optVar P R₁) R₂ = optVar (optVar P R₂) R₁
