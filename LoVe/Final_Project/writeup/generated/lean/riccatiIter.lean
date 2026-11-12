/-- Prior variance after `n` steps from initial variance `P₀`. -/
def riccatiIter (a Q R P₀ : ℝ) : ℕ → ℝ
  | 0     => P₀
  | n + 1 => riccatiStep a Q R (riccatiIter a Q R P₀ n)
