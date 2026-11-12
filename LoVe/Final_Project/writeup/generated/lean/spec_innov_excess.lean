-- D: an omitted coordinate inflates the innovation variance (the 4x diagnostic)
/-- With `e ⟂ v` and `e + v ⟂ h`: `Var(e + v + h) = (Var e + Var v) + Var h`. -/
theorem spec_innov_excess {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v h : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hh : MemLp h 2 μ) (hev : IndepFun e v μ) (hind : IndepFun (e + v) h μ) :
    variance (e + v + h) μ = (variance e μ + variance v μ) + variance h μ
