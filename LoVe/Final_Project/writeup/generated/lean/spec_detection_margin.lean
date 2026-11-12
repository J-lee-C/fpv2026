-- F5: detection margin (exact form of the innovation-variance ratio)
/-- If `S = Var e + Var v > 0`, then `Var(e + v + h) / S = 1 + Var h / S`. -/
theorem spec_detection_margin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ)
    (hS : 0 < variance e μ + variance v μ) :
    variance (e + v + h) μ / (variance e μ + variance v μ)
      = 1 + variance h μ / (variance e μ + variance v μ)
