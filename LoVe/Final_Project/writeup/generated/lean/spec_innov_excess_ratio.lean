/-- If also `S = Var e + Var v > 0` and `Var h > 0`, then `Var(e + v + h) / S > 1`. -/
theorem spec_innov_excess_ratio {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) (hτ : 0 < variance h μ) :
    1 < variance (e + v + h) μ / (variance e μ + variance v μ)
