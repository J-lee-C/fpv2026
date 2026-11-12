/-- Detailed balance of the square-root rule: `pᵢ · rate(i → j) = pⱼ · rate(j → i)`. -/
theorem detailed_balance (κ pᵢ pⱼ : ℝ) (hi : 0 < pᵢ) (hj : 0 < pⱼ) :
    pᵢ * jumpRate κ pᵢ pⱼ = pⱼ * jumpRate κ pⱼ pᵢ := by
  unfold jumpRate
  rw [Real.sqrt_div hj.le, Real.sqrt_div hi.le]
  calc pᵢ * (κ * (√pⱼ / √pᵢ)) = κ * (pᵢ / √pᵢ) * √pⱼ := by ring
    _ = κ * (pⱼ / √pⱼ) * √pᵢ := by rw [Real.div_sqrt, Real.div_sqrt]; ring
    _ = pⱼ * (κ * (√pᵢ / √pⱼ)) := by ring
