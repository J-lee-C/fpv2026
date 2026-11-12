/-- Error variance after an update with gain K (slide 5). -/
def postVar (P R K : ℝ) : ℝ :=
  (1 - K)^2 * P + K^2 * R
