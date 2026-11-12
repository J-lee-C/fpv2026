/-- Transition matrix of a two-state Markov state model, switching probabilities `p`, `q`. -/
def msm (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - p, p; q, 1 - q]
