# The Kalman gain, verified

`Kalman.lean` formalizes the scalar Kalman update, seven extensions and two capstone
results taken from a switching-diffusion model of molecular dynamics. `presentation/` holds
the talk, and `writeup/` a LaTeX guide to the model and the proofs.

## Lean formalization

All the Lean work is in [`Kalman.lean`](Kalman.lean).

| Part | Contents | Who checks it |
|---|---|---|
| 1 | Core definitions `postVar`, `gain`, `optVar` | a human (HUMAN-VERIFIED) |
| 2 | Core theorems `denom_pos`, `complete_square`, `postVar_gain`, `gain_optimal`, `gain_unique`, `optVar_le` | Lean |
| 3 | Model definitions `updErr`, `ouPredict`, `ouRiccati`, `innovCov`, `msm`, `switchCov`, `riccatiStep`, `riccatiIter`, `steadyVar`, `jumpRate`, `generator` | a human (HUMAN-VERIFIED) |
| 4 | Proofs for S (fusion), O (OU bound), W (white innovations), H0, H (switch) | Lean |
| 4b | Proofs for F: the filter forgets its start, converges, and is calibrated | Lean |
| 4c | Proofs for M: detailed balance (M1) and stationary populations (M2) | Lean |
| 5 | Proofs for A (variance formula), D (omitted coordinate) and F5 (exact detection margin), with random variables | Lean |
| 6 | The 17 `spec_*` statements, each proved in one line from an earlier Part | a human reads the statements; Lean the proofs |

Build it from the repository root, the folder that holds `lakefile.toml`:

```
lake exe cache get
lake build LoVe.Final_Project.Kalman
```

`lake exe cache get` (first time only) downloads Mathlib's compiled files. The repository
pins Lean and Mathlib v4.33.0. A plain `lake build` builds only `LoVe.lean`, which imports
Mathlib and nothing from this folder, so name the module. The build has no errors, no
warnings and no `sorry`; each `#print axioms` line reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Proof strategies

* **Core (`gain_optimal`, `gain_unique`, `optVar_le`).** Completing the square gives
  `postVar P R K = (P + R)(K - gain P R)² + optVar P R`, so the update variance exceeds its
  value at the Kalman gain by a nonnegative square, and equality forces the square, hence
  `K - gain P R`, to vanish. After clearing the positive denominator `P + R`,
  `optVar P R ≤ P` becomes `P R ≤ P (P + R)`, true since `R ≤ P + R` and `P ≥ 0`, and
  `optVar P R ≤ R` becomes `P R ≤ R (P + R)`, which `nlinarith` closes.
* **S (`fusion_comm`, `fusion_mono`).** Both fusion orders simplify to
  `P R₁ R₂ / (P R₁ + P R₂ + R₁ R₂)`, which is symmetric in `R₁` and `R₂`. Monotonicity is
  `optVar_le` applied to the nonnegative prior `optVar P R₁`.
* **O (`ou_bound`).** Induction on the step: if `0 ≤ x ≤ σ2`, the update gives
  `0 ≤ optVar x R ≤ x ≤ σ2`, and the prediction `a² y + σ2 (1 - a²)` is a weighted average
  of a value in `[0, σ2]` and `σ2` itself because `0 ≤ a² ≤ 1`.
* **A (`variance_update`, `variance_update_optimal`).** Write the update error as
  `(1 - K) • e + (-K) • v`; scaled copies of independent variables stay independent, so the
  sum rule and the scaling rule give `(1 - K)² Var e + K² Var v`. Optimality then follows
  from `gain_optimal` with `P = Var e ≥ 0` and `R = Var v > 0`.
* **D (`innov_excess`, `innov_excess_ratio`).** Apply the variance sum rule to `(e + v) + h`
  and then to `e + v`. The ratio exceeds 1 because `S < S + Var h` and `S > 0`.
* **W (`white_iff`).** By induction, lag `k + 1` equals `(a(1 - K))^k` times lag 1, and lag 1
  equals `a (P + R)(gain P R - K)`. If every lag vanishes, lag 1 does, so `K = gain P R`
  (as `a ≠ 0` and `P + R > 0`); conversely, at the Kalman gain lag 1 is 0, so every lag is 0.
* **H0 (`msm_eigen`).** Compute both entries of the matrix-vector product:
  `(1-p)p - pq = p(1-p-q)` and `qp - (1-q)q = -q(1-p-q)`.
* **H (`switch_ratio`).** Solve the recursion: `switchCov n = (c₁ - B) αⁿ + B lamⁿ` with
  `B = β lam / (lam - α) ≠ 0`. Since `|α / lam| < 1`, `switchCov n / lamⁿ → B`, and the ratio
  of successive lags is `lam` times a ratio of two sequences that both tend to `B`.
* **M1 (`detailed_balance`).** Split `√(pⱼ / pᵢ) = √pⱼ / √pᵢ` and use `pᵢ / √pᵢ = √pᵢ`;
  both sides become `κ √pᵢ √pⱼ`.
* **M2 (`populations_stationary`).** Entry `j` of `pᵀ L` is `p j L j j` plus the sum over
  `i ≠ j` of `p i · rate(i → j)`. Detailed balance and `κ i j = κ j i` turn each term of that
  sum into `p j · rate(j → i)`, so the sum is `p j` times the row's outflow, which the
  diagonal entry cancels.
* **F (`filter_guarantee`).** For `x, y ≥ 0`,
  `optVar x R - optVar y R = R² / ((x + R)(y + R)) · (x - y)` with a factor in `[0, 1]`, so one
  step shrinks gaps by `a²`; induction gives the `(a²)ⁿ` bound, since iterates stay `≥ 0`.
  `steadyVar ≥ 0` because `√D ≥ |Q - R(1 - a²)|`, and it solves the fixed-point quadratic, so
  a run started there stays there; the bound against that run squeezes `|Pₙ - P∞|` to 0.
  Calibration is the backward direction of `white_iff` at `P = steadyVar`.
* **F5 (`detection_margin`).** Rewrite the numerator with `innov_excess`, then
  `(S + τ²) / S = 1 + τ² / S` because `S ≠ 0`.

## Presentation

Open [`presentation/index.html`](presentation/index.html) in a browser (it loads reveal.js
and KaTeX from the jsDelivr CDN, so it needs an internet connection). Use the arrow keys to
move, `F` for full screen and `Esc` for the overview.

Regenerate every figure, and the numbers quoted on the slides, with

```
cd presentation
python make_figures.py
```

This needs numpy and matplotlib, uses fixed seeds, and writes `figures/fig01..fig14*.png`
and `figures/numbers.js`. Figures 9 and 10 are parsed from `Kalman.lean`; figures 11 to 14
illustrate the capstones (filter convergence, burn-in, detection margin, and a numerical
check of M2 on a three-basin generator).

## Write-up

[`writeup/kalman_writeup.tex`](writeup/kalman_writeup.tex) explains the project to a reader
with no physics or chemistry background:
- Part I builds the model from scratch: configurations, energy landscapes, basins, the
  switching diffusion, the OU process, sensors, the Kalman filter, and innovations.
- Part II lists what should be proved, what each result assumes, and what the results mean
  for an MD run.
- Part III shows the Lean definitions and the 17 final statements verbatim, each with a
  plain-language reading.
- Appendix A sketches every proof.

The compiled guide is [`writeup/kalman_writeup.pdf`](writeup/kalman_writeup.pdf). To rebuild
it, compile the `.tex` with pdfLaTeX, XeLaTeX, LuaLaTeX or Tectonic, twice so the contents
settle. In VS Code this needs a TeX engine and the LaTeX Workshop extension; with
[Tectonic](https://tectonic-typesetting.github.io) as the engine, saving the file rebuilds the
PDF. To regenerate the figures, the quoted numbers and the Lean excerpts:

```
cd writeup
python make_writeup_figures.py
```

This needs numpy and matplotlib, uses fixed seeds and takes 5 to 15 minutes. It imports the Lean
transcriptions from `presentation/make_figures.py` and copies each excerpt from `Kalman.lean`
into `writeup/generated/lean/`, so the document always shows the file's exact text.
`writeup/build_record.txt` holds the `#print axioms` output of the last build.

## AI assistance

* **Student:** Part 1 (the core definitions) and Part 2 (the core statements and all six
  proofs), copied verbatim from the student's `Core.lean` in this folder. The student
  reviewed Parts 1, 3 and 6.
* **Claude Code:**
  * Added the Part 2 docstrings. While the student's `Core.lean` still had five `sorry`s,
    an earlier version of this file used proofs by Claude Code; once the student finished
    `Core.lean`, Part 2 switched to the student's proofs, unchanged.
  * Parts 3 and 6 use the definitions and statements supplied in the two prompts (the
    extensions, then the capstones), verbatim; Claude Code added the Part 6 docstrings.
  * Claude Code wrote all of Parts 4, 4b, 4c and 5, the presentation (`index.html`,
    `make_figures.py`, the figures) and the write-up (`writeup/`). The F5 lemma sits in
    Part 5, not Part 4b, because it cites `innov_excess` from Part 5.
  * Claude Code first built the file in a separate Lake project on Lean and Mathlib
    v4.36.0-rc2, then moved it here and rebuilt it on this repository's v4.33.0.
* **Modeling notes.** S (fusion), O (OU bound), A (variance formula) and D (omitted
  coordinate) formalize scalar linear-Gaussian pieces of the switching-diffusion model
  directly. W (white innovations) holds for linear filters at steady state. H0 and H describe
  only the constant-rate two-state approximation of the hidden switch, not the diffusion's
  state-dependent jump rule. M covers the square-root jump rule, but only at a fixed slow
  state: it shows the basin populations are stationary for the jump process with the slow
  coordinates frozen, not that the full switching diffusion has the intended joint
  equilibrium. F assumes a scalar mode with known, constant `a`, `Q` and `R`. The recursions
  `ouRiccati`, `riccatiIter`, `innovCov` and `switchCov` are definitions of second moments,
  not derived from a stochastic process; only A, D and F5 use random variables. The slides'
  noise floor `3√(2/N)` for detecting an omitted coordinate is standard sampling theory, not
  a Lean result.
