-- A: the variance formula from random variables
/-- For independent `e`, `v` in `L²`: `Var((1 - K) e - K v) = postVar (Var e) (Var v) K`. -/
theorem spec_variance_update {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (K : ℝ) :
    variance (updErr K e v) μ = postVar (variance e μ) (variance v μ) K
