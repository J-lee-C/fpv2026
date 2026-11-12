/-- Steady-state innovation autocovariance at lag `k + 1`.
Lag 1 is `a(1-K)P - aKR`; each further lag multiplies by the filter pole `a(1-K)`. -/
def innovCov (a P R K : ℝ) : ℕ → ℝ
  | 0     => a * (1 - K) * P - a * K * R
  | k + 1 => a * (1 - K) * innovCov a P R K k
