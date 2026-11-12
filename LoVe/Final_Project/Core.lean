import Mathlib

noncomputable section
namespace Kalman

/-- Error variance after an update with gain K (slide 5). -/
def postVar (P R K : ℝ) : ℝ :=
  (1 - K)^2 * P + K^2 * R

/-- The Kalman gain (slide 6). -/
def gain (P R : ℝ) : ℝ := P / (P + R)

/-- The smallest possible variance, f(K*) (slide 6). -/
def optVar (P R : ℝ) : ℝ := P * R / (P + R)

/-! ### Lemma ladder (slide 10) -/

theorem denom_pos (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    0 < P + R := by
  linarith

theorem complete_square (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R K = (P + R) * (K - gain P R)^2 + optVar P R := by
  unfold gain optVar postVar
  have pos := denom_pos P R hP hR
  field_simp
  ring

theorem postVar_gain (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) = optVar P R := by
  unfold postVar gain optVar
  field

/-! ### Main theorems -/

theorem gain_optimal (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    postVar P R (gain P R) ≤ postVar P R K := by
  have comp_sq := complete_square P R K hP hR
  have pvg := postVar_gain P R hP hR
  rw [comp_sq]
  rw [pvg]
  rw [le_add_iff_nonneg_left]
  have pos := denom_pos P R hP hR
  have square_plus := sq_nonneg (K - gain P R)
  have pos_or_zero := le_of_lt pos
  apply mul_nonneg pos_or_zero square_plus

theorem gain_unique (P R K : ℝ) (hP : 0 ≤ P) (hR : 0 < R)
    (h : postVar P R K = postVar P R (gain P R)) : K = gain P R := by
  have pos := denom_pos P R hP hR
  have comp_sq := complete_square P R K hP hR
  have pvg := postVar_gain P R hP hR
  rw[pvg] at h
  rw[comp_sq] at h
  rw[add_eq_right] at h
  cases mul_eq_zero.mp h with
  |inl impos => linarith
  |inr solve =>
    have zero : K - gain P R = 0 := by exact eq_zero_of_pow_eq_zero solve
    apply sub_eq_zero.mp zero

theorem optVar_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    optVar P R ≤ P ∧ optVar P R ≤ R := by
  have pos := denom_pos P R hP hR
  unfold optVar
  field_simp
  constructor
  · have R_plus_P: R≤P+R := by linarith
    exact mul_le_mul_of_nonneg_left R_plus_P hP
  · nlinarith

end Kalman
