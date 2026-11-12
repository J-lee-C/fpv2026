-- H0, H (stretch): the hidden switch's fingerprint
/-- `(p, -q)` is an eigenvector of the MSM transition matrix with eigenvalue `1 - p - q`. -/
theorem spec_msm_eigen (p q : ℝ) :
    (msm p q).mulVec ![p, -q] = (1 - p - q) • ![p, -q]
