/-- Jump rate from a basin with population density `pᵢ` to one with `pⱼ`:
symmetric prefactor `κ` times `sqrt (pⱼ / pᵢ)`. -/
def jumpRate (κ pᵢ pⱼ : ℝ) : ℝ := κ * Real.sqrt (pⱼ / pᵢ)
