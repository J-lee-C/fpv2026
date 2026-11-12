/-- Prediction step for one OU mode: decay `a`, stationary (equilibrium) variance `σ2`. -/
def ouPredict (a σ2 P : ℝ) : ℝ := a ^ 2 * P + σ2 * (1 - a ^ 2)
