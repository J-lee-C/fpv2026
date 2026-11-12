/-- Generator of basin switching at a fixed slow state: off-diagonal entries are jump
rates, each diagonal entry is minus its row's total outflow. -/
def generator {n : ℕ} (κ : Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then -(∑ k ∈ Finset.univ.erase i, jumpRate (κ i k) (p i) (p k))
             else jumpRate (κ i j) (p i) (p j)
