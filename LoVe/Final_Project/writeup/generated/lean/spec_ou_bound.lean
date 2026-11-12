-- O: an OU mode is never tracked worse than its equilibrium spread
/-- For `a² ≤ 1`, the OU prior variance stays in `[0, σ2]` at every step `n`. -/
theorem spec_ou_bound (a σ2 R : ℝ) (ha : a ^ 2 ≤ 1) (hσ : 0 ≤ σ2) (hR : 0 < R) (n : ℕ) :
    0 ≤ ouRiccati a σ2 R n ∧ ouRiccati a σ2 R n ≤ σ2
