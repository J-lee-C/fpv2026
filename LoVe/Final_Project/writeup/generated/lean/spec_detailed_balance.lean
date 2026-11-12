-- M1: the square-root rule satisfies detailed balance
/-- For positive populations, `pᵢ · rate(i → j) = pⱼ · rate(j → i)`. -/
theorem spec_detailed_balance (κ pᵢ pⱼ : ℝ) (hi : 0 < pᵢ) (hj : 0 < pⱼ) :
    pᵢ * jumpRate κ pᵢ pⱼ = pⱼ * jumpRate κ pⱼ pᵢ
