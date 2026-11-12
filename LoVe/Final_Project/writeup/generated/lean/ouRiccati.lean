/-- Prior variance of an OU mode under the optimal filter, started at equilibrium `σ2`. -/
def ouRiccati (a σ2 R : ℝ) : ℕ → ℝ
  | 0     => σ2
  | n + 1 => ouPredict a σ2 (optVar (ouRiccati a σ2 R n) R)
