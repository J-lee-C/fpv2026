/-- If `Var v > 0`, the gain `Var e / (Var e + Var v)` minimizes the update error's variance. -/
theorem spec_variance_update_optimal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (hR : 0 < variance v μ) (K : ℝ) :
    variance (updErr (gain (variance e μ) (variance v μ)) e v) μ
      ≤ variance (updErr K e v) μ
