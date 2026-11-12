/-- One step of the scalar filter variance: optimal update with noise `R`, then predict
with decay `a` and process noise `Q`. -/
def riccatiStep (a Q R P : ℝ) : ℝ := a ^ 2 * optVar P R + Q
