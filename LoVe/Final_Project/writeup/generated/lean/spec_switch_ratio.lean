/-- If `β ≠ 0` and `|α| < |lam|`, the ratio of successive lags tends to `lam`. -/
theorem spec_switch_ratio (α β lam c₁ : ℝ) (hβ : β ≠ 0) (hlt : |α| < |lam|) :
    Tendsto (fun n => switchCov α β lam c₁ (n + 1) / switchCov α β lam c₁ n)
      atTop (𝓝 lam)
