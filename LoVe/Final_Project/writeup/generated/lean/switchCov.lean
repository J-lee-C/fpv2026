/-- Innovation autocovariance at lag `n + 1` when an unmodeled switch with eigenvalue `lam`
leaks into the innovations with strength `β`; `α` is the filter pole, `c₁` the lag-1 value. -/
def switchCov (α β lam c₁ : ℝ) : ℕ → ℝ
  | 0     => c₁
  | n + 1 => α * switchCov α β lam c₁ n + β * lam ^ (n + 1)
