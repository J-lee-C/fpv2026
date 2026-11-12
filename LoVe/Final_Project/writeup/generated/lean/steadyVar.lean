/-- Steady-state prior variance: the nonnegative root of `P² + (R(1-a²) - Q)P - QR = 0`. -/
def steadyVar (a Q R : ℝ) : ℝ :=
  ((Q - R * (1 - a ^ 2)) + Real.sqrt ((R * (1 - a ^ 2) - Q) ^ 2 + 4 * Q * R)) / 2
