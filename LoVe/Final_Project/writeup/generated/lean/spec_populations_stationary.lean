-- M2: the target populations are stationary for the switching generator
/-- With symmetric `κ` and positive `p`, the populations satisfy `pᵀ L = 0`. -/
theorem spec_populations_stationary {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hκ : ∀ i j, κ i j = κ j i) (hp : ∀ i, 0 < p i) :
    Matrix.vecMul p (generator κ p) = 0
