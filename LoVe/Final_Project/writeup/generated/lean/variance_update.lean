/-- `Var((1 - K) e - K v) = (1 - K)² Var e + K² Var v` for independent `e`, `v` in `L²`. -/
theorem variance_update {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e v : Ω → ℝ} (he : MemLp e 2 μ) (hv : MemLp v 2 μ)
    (hind : IndepFun e v μ) (K : ℝ) :
    variance (updErr K e v) μ = postVar (variance e μ) (variance v μ) K := by
  have hind' : IndepFun ((1 - K) • e) ((-K) • v) μ :=
    hind.comp (measurable_const_mul (1 - K)) (measurable_const_mul (-K))
  rw [updErr_eq, hind'.variance_add (he.const_smul (1 - K)) (hv.const_smul (-K)),
    variance_smul, variance_smul, postVar]
  ring
