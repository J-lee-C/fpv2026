-- F: the filter forgets its start, converges, and is calibrated at steady state
/-- For `a² < 1`: gaps shrink like `(a²)ⁿ`; `steadyVar` is the fixed point, limit, and white. -/
theorem spec_filter_guarantee (a Q R : ℝ) (ha : a ^ 2 < 1) (ha0 : a ≠ 0)
    (hQ : 0 ≤ Q) (hR : 0 < R) :
    (∀ P₀ P₀' : ℝ, 0 ≤ P₀ → 0 ≤ P₀' → ∀ n,
      |riccatiIter a Q R P₀ n - riccatiIter a Q R P₀' n| ≤ (a ^ 2) ^ n * |P₀ - P₀'|) ∧
    (0 ≤ steadyVar a Q R ∧ riccatiStep a Q R (steadyVar a Q R) = steadyVar a Q R) ∧
    (∀ P₀ : ℝ, 0 ≤ P₀ → Tendsto (riccatiIter a Q R P₀) atTop (𝓝 (steadyVar a Q R))) ∧
    (∀ k, innovCov a (steadyVar a Q R) R (gain (steadyVar a Q R) R) k = 0)
