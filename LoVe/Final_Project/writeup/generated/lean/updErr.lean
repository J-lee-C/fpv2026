/-- Error after an update with gain `K`, from prediction error `e` and sighting noise `v`. -/
def updErr {Ω : Type*} (K : ℝ) (e v : Ω → ℝ) : Ω → ℝ :=
  fun ω => (1 - K) * e ω - K * v ω
