/-- With symmetric prefactors the target populations are stationary: `pᵀ L = 0`. -/
theorem populations_stationary {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hκ : ∀ i j, κ i j = κ j i) (hp : ∀ i, 0 < p i) :
    Matrix.vecMul p (generator κ p) = 0 := by
  ext j
  have hflow : ∀ i ∈ Finset.univ.erase j,
      p i * generator κ p i j = p j * jumpRate (κ j i) (p j) (p i) := by
    intro i hi
    simp only [generator, if_neg (Finset.ne_of_mem_erase hi), hκ i j]
    exact detailed_balance _ _ _ (hp i) (hp j)
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Finset.sum_congr rfl hflow,
    ← Finset.mul_sum]
  dsimp only [generator]
  rw [if_pos rfl]
  ring
