/-- The Kalman gain (slide 6). -/
def gain (P R : ℝ) : ℝ := P / (P + R)
