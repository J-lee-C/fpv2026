"""Make every figure for the Kalman presentation.

    python make_figures.py

Writes figures/fig01..fig14 (*.png) and figures/numbers.js, which holds every number
the slides quote (the deck fills its %%key%% placeholders from it). Fixed seeds;
numpy and matplotlib only. Figures 9 and 10 are parsed from ../Kalman.lean.
"""
from __future__ import annotations

import itertools
import json
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch, Rectangle  # noqa: E402

HERE = Path(__file__).resolve().parent
FIG = HERE / "figures"
LEAN = HERE.parent / "Kalman.lean"

# Reference data-viz palette (validated: slots 1-3 pass all-pairs CVD checks; the
# ordinal blue ramp passes the ordinal checks). Text always uses the ink colors.
SURFACE = "#fcfcfb"
INK, INK2, MUTED = "#0b0b0b", "#52514e", "#898781"
GRID, AXIS = "#e1e0d9", "#c3c2b7"
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
RAMP = ["#86b6ef", "#5598e7", "#2a78d6", "#1c5cab", "#0d366b"]
NEUTRAL = "#c3c2b7"
# Copied from the `#print axioms` output of Kalman.lean (identical for all 17 results).
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

NUM: dict[str, str] = {}


# ----------------------------------------------------------------------------------------
# The Lean definitions, transcribed (Parts 1 and 3 of Kalman.lean).
def post_var(P, R, K):
    return (1 - K) ** 2 * P + K ** 2 * R


def gain(P, R):
    return P / (P + R)


def opt_var(P, R):
    return P * R / (P + R)


def ou_predict(a, s2, P):
    return a ** 2 * P + s2 * (1 - a ** 2)


def ou_riccati(a, s2, R, n):
    """[ouRiccati a σ2 R 0, ..., ouRiccati a σ2 R n]."""
    out = [s2]
    for _ in range(n):
        out.append(ou_predict(a, s2, opt_var(out[-1], R)))
    return out


def riccati_step(a, Q, R, P):
    return a ** 2 * opt_var(P, R) + Q


def riccati_iter(a, Q, R, P0, n):
    """[riccatiIter a Q R P₀ 0, ..., riccatiIter a Q R P₀ n]."""
    out = [P0]
    for _ in range(n):
        out.append(riccati_step(a, Q, R, out[-1]))
    return np.array(out)


def steady_var(a, Q, R):
    return ((Q - R * (1 - a ** 2)) + np.sqrt((R * (1 - a ** 2) - Q) ** 2 + 4 * Q * R)) / 2


def jump_rate(kappa, p_i, p_j):
    return kappa * np.sqrt(p_j / p_i)


def generator(kappa, p):
    """generator κ p: off-diagonal jump rates, diagonal minus the row's total outflow."""
    n = len(p)
    L = np.array([[jump_rate(kappa[i, j], p[i], p[j]) if i != j else 0.0 for j in range(n)]
                  for i in range(n)])
    return L - np.diag(L.sum(axis=1))


# ----------------------------------------------------------------------------------------
def setup_style():
    plt.rcParams.update({
        "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
        "font.family": "sans-serif",
        "font.sans-serif": ["Segoe UI", "DejaVu Sans", "Arial"],
        "font.monospace": ["Consolas", "DejaVu Sans Mono"],
        "mathtext.fontset": "dejavusans",
        "font.size": 13, "axes.titlesize": 14, "axes.labelsize": 13,
        "axes.edgecolor": AXIS, "axes.linewidth": 0.8, "axes.labelcolor": INK2,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8, "grid.linestyle": "-",
        "axes.axisbelow": True,
        "xtick.color": AXIS, "ytick.color": AXIS,
        "xtick.labelcolor": INK2, "ytick.labelcolor": INK2,
        "lines.linewidth": 2.0, "lines.solid_capstyle": "round",
        "lines.solid_joinstyle": "round",
        "legend.frameon": False, "legend.fontsize": 12, "text.color": INK,
    })


def save(fig, name):
    fig.savefig(FIG / name, dpi=150, bbox_inches="tight", pad_inches=0.15)
    plt.close(fig)
    print("wrote", FIG / name)


def end_dot(ax, x, y, color):
    """An 8px end marker with a 2px surface ring."""
    ax.plot([x], [y], "o", ms=8, color=color, mec=SURFACE, mew=2, zorder=5)


def fmt(x, digits=2):
    return f"{x:.{digits}f}"


def tint(hex_color, alpha):
    """The color `alpha` of the way from the surface to `hex_color` (an opaque wash)."""
    c = np.array([int(hex_color[i:i + 2], 16) for i in (1, 3, 5)], float)
    s = np.array([int(SURFACE[i:i + 2], 16) for i in (1, 3, 5)], float)
    m = np.round(s + alpha * (c - s)).astype(int)
    return "#" + "".join(f"{v:02x}" for v in m)


# ----------------------------------------------------------------------------------------
def fig01_fusion():
    """Prediction (P), sighting (R) and fused estimate (PR/(P+R)) as Gaussians."""
    P, R, mu_pred, y = 4.0, 1.0, 0.0, 3.0
    K, var_f = gain(P, R), opt_var(P, R)
    mu_f = mu_pred + K * (y - mu_pred)
    x = np.linspace(-6.5, 7.5, 800)

    def pdf(m, v):
        return np.exp(-(x - m) ** 2 / (2 * v)) / np.sqrt(2 * np.pi * v)

    fig, ax = plt.subplots(figsize=(10, 4.4))
    series = [(mu_pred, P, BLUE, f"prediction: variance P = {P:g}"),
              (y, R, ORANGE, f"sighting: variance R = {R:g}"),
              (mu_f, var_f, AQUA, f"fused: variance PR/(P+R) = {var_f:g}")]
    for m, v, c, lab in series:
        ax.plot(x, pdf(m, v), color=c, label=lab)
        ax.fill_between(x, pdf(m, v), color=c, alpha=0.10, lw=0)
    for m, v, name, dx in [(mu_pred, P, "prediction", -0.3), (y, R, "sighting", 0.45),
                           (mu_f, var_f, "fused", -0.35)]:
        peak = 1 / np.sqrt(2 * np.pi * v)
        ax.text(m + dx, peak + 0.012, name, ha="right" if dx < 0 else "left",
                va="bottom", color=INK2, fontsize=12)
    ax.set_xlabel("position")
    ax.set_ylabel("probability density")
    ax.set_ylim(0, 0.56)
    ax.legend(loc="upper left")
    save(fig, "fig01_fusion.png")
    NUM.update(f1_P=f"{P:g}", f1_R=f"{R:g}", f1_K=f"{K:g}", f1_var=f"{var_f:g}",
               f1_pred=f"{mu_pred:g}", f1_y=f"{y:g}", f1_fused=f"{mu_f:g}")


def fig02_parabola():
    """f(K) = postVar P R K, its minimum at K*, and the gap (P+R)(K-K*)^2."""
    P, R = 4.0, 1.0
    Ks, fs = gain(P, R), opt_var(P, R)
    K = np.linspace(-0.1, 1.35, 500)
    f = post_var(P, R, K)
    fig, ax = plt.subplots(figsize=(10, 4.6))
    ax.fill_between(K, fs, f, color=ORANGE, alpha=0.16, lw=0,
                    label=r"gap $(P+R)(K-K^*)^2$")
    ax.plot(K, f, color=BLUE, label=r"$f(K) = (1-K)^2P + K^2R$")
    ax.axhline(fs, color=INK2, lw=1.2, ls=(0, (4, 3)),
               label=r"minimum $f(K^*) = PR/(P+R)$")
    end_dot(ax, Ks, fs, BLUE)
    ax.annotate(rf"$K^* = P/(P+R) = {Ks:g}$", xy=(Ks, fs), xytext=(Ks + 0.06, fs + 1.25),
                color=INK, fontsize=13,
                arrowprops=dict(arrowstyle="-", color=INK2, lw=1))
    K0 = 0.25
    ax.annotate("", xy=(K0, post_var(P, R, K0)), xytext=(K0, fs),
                arrowprops=dict(arrowstyle="<->", color=INK2, lw=1.2, shrinkA=0, shrinkB=0))
    ax.text(K0 + 0.025, (fs + post_var(P, R, K0)) / 2, r"$(P+R)(K-K^*)^2$",
            color=INK, fontsize=13, va="center")
    ax.set_xlabel("gain K")
    ax.set_ylabel("variance after the update")
    ax.set_ylim(0, 4.6)
    ax.legend(loc="upper right")
    save(fig, "fig02_parabola.png")
    NUM.update(f2_Kstar=f"{Ks:g}", f2_fmin=f"{fs:g}", f2_PR=f"{P + R:g}")


def fig03_ratio():
    """K* and the minimum variance (relative to P) against the noise ratio R/P."""
    r = np.logspace(-2, 2, 500)
    fig, ax = plt.subplots(figsize=(10, 4.4))
    ax.plot(r, 1 / (1 + r), color=BLUE, label=r"gain $K^* = P/(P+R)$")
    ax.plot(r, r / (1 + r), color=ORANGE, label=r"minimum variance $\frac{PR}{P+R}\,/\,P$")
    r0 = 1.0 / 4.0   # the example of fig 1: P = 4, R = 1
    for val, col in [(1 / (1 + r0), BLUE), (r0 / (1 + r0), ORANGE)]:
        end_dot(ax, r0, val, col)
    ax.text(r0 * 1.15, 1 / (1 + r0) + 0.03, "example: R/P = 1/4", color=INK2, fontsize=11)
    ax.text(1.15, 0.5, "equal trust at R = P", color=INK2, fontsize=11, va="center")
    ax.text(95, 0.42, "large R/P:\ntrust the prediction", color=INK2, fontsize=11,
            ha="right", va="center")
    ax.text(0.0105, 0.42, "small R/P:\ntrust the sighting", color=INK2, fontsize=11,
            va="center")
    ax.set_xscale("log")
    ax.set_xlabel("noise ratio R / P (log scale)")
    ax.set_ylabel("fraction")
    ax.set_ylim(0, 1.05)
    ax.legend(loc="center left", bbox_to_anchor=(0.0, 0.62))
    save(fig, "fig03_ratio.png")


def fig04_sensors():
    """Fusing sensors in two orders: same end point, never increasing."""
    P0 = 4.0
    Rs = [2.0, 0.5, 3.0, 1.0, 1.5]

    def path(order):
        out = [P0]
        for R in order:
            out.append(opt_var(out[-1], R))
        return out

    a, b = path(Rs), path(Rs[::-1])
    closed = 1 / (1 / P0 + sum(1 / R for R in Rs))
    finals = [path(list(p))[-1] for p in itertools.permutations(Rs)]
    spread = max(finals) - min(finals)
    steps = np.arange(len(Rs) + 1)
    fig, ax = plt.subplots(figsize=(10, 4.4))
    ax.plot(steps, a, color=BLUE, marker="o", ms=8, mec=SURFACE, mew=2,
            label="order R = " + ", ".join(f"{R:g}" for R in Rs))
    ax.plot(steps, b, color=ORANGE, marker="o", ms=8, mec=SURFACE, mew=2,
            label="reversed order R = " + ", ".join(f"{R:g}" for R in Rs[::-1]))
    ax.axhline(closed, color=INK2, lw=1.2, ls=(0, (4, 3)),
               label=r"precisions add: $1/(1/P + \sum_i 1/R_i)$")
    ax.text(len(Rs) + 0.2, closed + 0.06, f"{closed:.4f}", color=INK, va="bottom",
            fontsize=12)
    ax.set_xticks(steps, ["prior"] + [f"+{k}" for k in steps[1:]])
    ax.set_xlabel("sensors fused so far")
    ax.set_ylabel("variance")
    ax.set_xlim(-0.2, len(Rs) + 0.6)
    ax.set_ylim(0, P0 * 1.08)
    ax.legend(loc="upper right")
    save(fig, "fig04_sensors.png")
    NUM.update(f4_P0=f"{P0:g}", f4_Rs=", ".join(f"{R:g}" for R in Rs),
               f4_n=str(len(Rs)), f4_final=f"{closed:.4f}",
               f4_norders=str(len(finals)),
               f4_spread="exactly" if spread == 0 else f"to within {spread:.0e} (rounding)")


def fig05_ou():
    """ouRiccati over the steps for several decays a: always inside [0, σ2]."""
    s2, R, n = 1.0, 0.5, 40
    avals = [0.0, 0.5, 0.9, 0.99, 1.0]
    fig, ax = plt.subplots(figsize=(10, 4.6))
    ax.axhspan(0, s2, color=tint(BLUE, 0.07), lw=0, zorder=0)
    ax.text(n + 0.4, s2 - 0.02, r"allowed band $[0, \sigma_2]$", color=INK2, fontsize=11,
            va="top")
    steps = np.arange(n + 1)
    for a, col in zip(avals, RAMP):
        vals = ou_riccati(a, s2, R, n)
        ax.plot(steps, vals, color=col, label=f"a = {a:g}")
        end_dot(ax, n, vals[-1], col)
        NUM[f"f5_end_{str(a).replace('.', '_')}"] = fmt(vals[-1], 3)
    ax.set_xlabel("filter step n")
    ax.set_ylabel(r"prior variance  ouRiccati a $\sigma_2$ R n")
    ax.set_xlim(0, n + 9)
    ax.set_ylim(-0.03, 1.1)
    ax.legend(title="OU decay", loc="center right", title_fontsize=12)
    save(fig, "fig05_ou.png")
    NUM.update(f5_s2=f"{s2:g}", f5_R=f"{R:g}", f5_n=str(n),
               f5_avals=", ".join(f"{a:g}" for a in avals))


def fig06_innovations():
    """Innovation-variance ratio per channel; one channel omits a hidden coordinate."""
    rng = np.random.default_rng(6)
    P = 0.6
    Rc = np.array([0.4, 0.8, 0.5, 1.0, 0.3, 0.6])
    flagged = 3                       # channel 4 omits the hidden coordinate h
    S = P + Rc                        # predicted innovation variance Var e + Var v
    tau2 = 3 * S[flagged]             # Var h, chosen so that the theory value is 4
    N = 200_000
    e = rng.normal(0, np.sqrt(P), N)  # shared prediction error
    ratios = []
    for c in range(len(Rc)):
        nu = e + rng.normal(0, np.sqrt(Rc[c]), N)
        if c == flagged:
            nu = nu + rng.normal(0, np.sqrt(tau2), N)
        ratios.append(nu.var() / S[c])
    ratios = np.array(ratios)
    theory = 1 + tau2 / S[flagged]
    xs = np.arange(1, len(Rc) + 1)
    fig, ax = plt.subplots(figsize=(10, 4.6))
    ax.set_xlim(0.4, len(Rc) + 0.6)
    ax.set_ylim(0, 4.7)
    ax.set_xticks(xs, [f"channel {k}" for k in xs])
    for k, rv in zip(xs, ratios):
        ax.bar(k, rv, width=0.36, color=BLUE if k - 1 == flagged else NEUTRAL, lw=0,
               zorder=3)
        target = theory if k - 1 == flagged else 1.0
        ax.plot([k - 0.3, k + 0.3], [target, target], color=INK, lw=1.4, ls=(0, (3, 2)),
                zorder=4)
    kf = flagged + 1
    ax.text(kf + 0.33, theory, rf"theory $1 + \tau^2/S$ = {theory:g}", color=INK,
            va="center", fontsize=12)
    ax.text(kf, ratios[flagged] / 2, f"{ratios[flagged]:.2f}", color="#ffffff",
            ha="center", va="center", fontsize=12, zorder=5, fontweight="bold")
    ax.text(1.0 - 0.3, 1.12, "theory 1", color=INK2, fontsize=11)
    ax.set_ylabel("innovation variance / predicted S")
    ax.set_title("Channel 4 omits a hidden coordinate h; the others are modeled correctly",
                 color=INK2, fontsize=12, loc="left")
    save(fig, "fig06_innovations.png")
    clean = np.delete(ratios, flagged)
    NUM.update(f6_N=f"{N:,}", f6_P=f"{P:g}", f6_Rflag=f"{Rc[flagged]:g}",
               f6_S=f"{S[flagged]:g}", f6_tau2=f"{tau2:g}", f6_theory=f"{theory:g}",
               f6_ratio=f"{ratios[flagged]:.2f}", f6_clean_lo=f"{clean.min():.3f}",
               f6_clean_hi=f"{clean.max():.3f}", f6_channels=str(len(Rc)),
               f6_flag=str(kf))


def two_state_chain(rng, p, q, n):
    """A two-state Markov chain in {+1, -1}: leave +1 w.p. p, leave -1 w.p. q, per step."""
    state = 1.0 if rng.random() < q / (p + q) else -1.0     # stationary start
    out = np.empty(n)
    i = 0
    while i < n:
        hold = int(rng.geometric(p if state > 0 else q))
        out[i:i + hold] = state
        i += hold
        state = -state
    return out


def innovations(z, alpha, ak):
    """Steady-state Kalman innovations: x⁻(t+1) = α x⁻(t) + aK z(t), ν(t) = z(t) - x⁻(t)."""
    nu = np.empty_like(z)
    xp = 0.0
    for t, zt in enumerate(z.tolist()):
        nu[t] = zt - xp
        xp = alpha * xp + ak * zt
    return nu


def acf(x, maxlag):
    x = x - x.mean()
    n = len(x)
    f = np.fft.rfft(x, 2 * n)
    c = np.fft.irfft(f * np.conj(f))[: maxlag + 1] / n
    return c / c[0]


def fig07_autocorr():
    """Innovation autocorrelation: correct filter vs a filter ignoring a hidden switch."""
    rng = np.random.default_rng(7)
    a, R, p, q, s2, amp = 0.5, 0.2, 0.02, 0.02, 1.0, 1.0
    N, burn, maxlag = 1_000_000, 1_000, 60
    P = s2
    for _ in range(1000):             # steady state of the Riccati map (as in ouRiccati)
        P = ou_predict(a, s2, opt_var(P, R))
    K = gain(P, R)
    alpha, lam2 = a * (1 - K), 1 - p - q
    s = two_state_chain(rng, p, q, N + burn)
    w = rng.normal(0, np.sqrt(s2 * (1 - a * a)), N + burn)
    x = np.empty(N + burn)
    xt = rng.normal(0, np.sqrt(s2))
    for t, wt in enumerate(w.tolist()):
        x[t] = xt
        xt = a * xt + wt
    y = x + amp * s + rng.normal(0, np.sqrt(R), N + burn)
    nu_naive = innovations(y, alpha, a * K)[burn:]
    nu_right = innovations(y - amp * s, alpha, a * K)[burn:]
    rho_naive, rho_right = acf(nu_naive, maxlag), acf(nu_right, maxlag)
    lags = np.arange(1, maxlag + 1)
    fit = np.arange(10, 51)
    slope, icept = np.polyfit(fit, np.log(rho_naive[fit]), 1)
    lam_hat = float(np.exp(slope))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.6))
    ax1.axhline(0, color=AXIS, lw=0.8)
    ax1.plot(lags, rho_naive[1:], color=ORANGE, label="filter ignores the switch")
    ax1.plot(lags, rho_right[1:], color=BLUE, label="filter knows the switch")
    ax1.set_xlabel("lag k")
    ax1.set_ylabel("innovation autocorrelation")
    ax1.legend(loc="upper right")
    ax1.set_title("Autocorrelation of the innovations", loc="left", color=INK2, fontsize=12)

    ax2.semilogy(lags, rho_naive[1:], "o", ms=5, color=ORANGE, mec=SURFACE, mew=1,
                 label="filter ignores the switch")
    kk = np.arange(1, maxlag + 1)
    ax2.semilogy(kk, np.exp(icept + slope * kk), color=INK, lw=1.4, ls=(0, (4, 3)),
                 label=rf"fit on lags 10 to 50: decay $\hat\lambda$ = {lam_hat:.3f}")
    ax2.set_xlabel("lag k")
    ax2.set_ylabel("autocorrelation (log scale)")
    ax2.legend(loc="upper right")
    ax2.set_title(rf"Tail decay vs switch eigenvalue $\lambda_2 = 1-p-q$ = {lam2:g}",
                  loc="left", color=INK2, fontsize=12)
    fig.tight_layout(w_pad=3)
    save(fig, "fig07_autocorr.png")
    NUM.update(f7_a=f"{a:g}", f7_R=f"{R:g}", f7_p=f"{p:g}", f7_q=f"{q:g}",
               f7_N=f"{N:,}", f7_lam2=f"{lam2:g}", f7_lamhat=f"{lam_hat:.3f}",
               f7_alpha=f"{alpha:.3f}", f7_K=f"{K:.3f}", f7_P=f"{P:.3f}",
               f7_rho1=f"{rho_naive[1]:.3f}",
               f7_right_max=f"{np.max(np.abs(rho_right[1:])):.4f}")


def fig08_msm():
    """The two-state Markov state model: states A and B, switching probabilities p, q."""
    p = q = 0.02
    lam2 = 1 - p - q
    fig, ax = plt.subplots(figsize=(9, 4.0))
    ax.set_xlim(0, 10)
    ax.set_ylim(0.2, 4.8)
    ax.set_aspect("equal")
    ax.axis("off")
    r = 0.85
    cA, cB = np.array([3.0, 2.8]), np.array([7.0, 2.8])
    for c, col, name in [(cA, BLUE, "A"), (cB, ORANGE, "B")]:
        ax.add_patch(Circle(c, r, facecolor=tint(col, 0.16), edgecolor=col, lw=2.2))
        ax.text(*c, name, ha="center", va="center", fontsize=26, color=INK)
    arrow = dict(arrowstyle="-|>", mutation_scale=20, color=INK2, lw=1.6)
    ax.add_patch(FancyArrowPatch(cA + [0.55, 0.65], cB + [-0.55, 0.65],
                                 connectionstyle="arc3,rad=-0.35", **arrow))
    ax.add_patch(FancyArrowPatch(cB + [-0.55, -0.65], cA + [0.55, -0.65],
                                 connectionstyle="arc3,rad=-0.35", **arrow))
    ax.text(5.0, 4.15, "p", ha="center", fontsize=20, color=INK, style="italic")
    ax.text(5.0, 1.25, "q", ha="center", fontsize=20, color=INK, style="italic")
    for c, sign, lab in [(cA, -1, "1 − p"), (cB, 1, "1 − q")]:
        start = c + [sign * r * np.cos(np.pi / 5), r * np.sin(np.pi / 5)]
        end = c + [sign * r * np.cos(np.pi / 5), -r * np.sin(np.pi / 5)]
        ax.add_patch(FancyArrowPatch(start, end,
                                     connectionstyle=f"arc3,rad={-2.2 * sign}", **arrow))
        ax.text(c[0] + sign * 1.95, c[1], lab, ha="left" if sign > 0 else "right",
                va="center", fontsize=16, color=INK, style="italic")
    ax.text(5.0, 0.35, rf"eigenvalues $\lambda_1 = 1$, $\lambda_2 = 1 - p - q$ "
                       rf"(p = q = {p:g}: $\lambda_2$ = {lam2:g})",
            ha="center", fontsize=14, color=INK2)
    save(fig, "fig08_msm.png")
    NUM.update(f8_p=f"{p:g}", f8_lam2=f"{lam2:g}")


# ----------------------------------------------------------------------------------------
def parse_lean():
    """Theorems of Kalman.lean with their Part, topic, and the theorems their proofs cite."""
    text = LEAN.read_text(encoding="utf-8")
    part, topic, order, info = None, None, [], {}
    blocks = re.split(r"(?m)^(?=/-! ## Part |/-! ### |theorem |def )", text)
    for blk in blocks:
        if m := re.match(r"/-! ## Part (\d[a-z]?)", blk):
            part, topic = m.group(1), None
        elif m := re.match(r"/-! ### (\w+):", blk):
            topic = m.group(1)
        elif m := re.match(r"theorem (\w+)", blk):
            body = re.split(r"(?m)^(?:/-|end )", blk)[0]
            info[m.group(1)] = dict(part=part, topic=topic or "Core", body=body)
            order.append(m.group(1))
        elif m := re.match(r"def (\w+)", blk):
            info.setdefault("_defs", []).append((m.group(1), part))
    defs = info.pop("_defs")
    names = set(order)
    for n in order:
        info[n]["uses"] = [u for u in order if u != n
                           and re.search(rf"(?<![\w.]){re.escape(u)}(?![\w])", info[n]["body"])]
    return order, info, defs, names


def fig09_dependencies():
    """Dependency graph of the Lean theorems, parsed from Kalman.lean."""
    order, info, _, _ = parse_lean()
    main = [n for n in order if not n.startswith("spec_")]
    cited = {u for n in order if n.startswith("spec_") for u in info[n]["uses"]}
    depth = {}

    def d(n):
        if n not in depth:
            depth[n] = 1 + max((d(u) for u in info[n]["uses"]), default=-1)
        return depth[n]

    for n in main:
        d(n)
    topics = []
    for n in main:
        if info[n]["topic"] not in topics:
            topics.append(info[n]["topic"])
    pos, row, bands = {}, 0, []
    for t in topics:
        nodes = [n for n in main if info[n]["topic"] == t]
        slots: dict[int, int] = {}
        for n in nodes:
            k = slots.get(depth[n], 0)
            pos[n] = (depth[n], row + k)
            slots[depth[n]] = k + 1
        height = max(slots.values())
        bands.append((t, row, height))
        row += height
    part_color = {"2": BLUE, "4": ORANGE, "4b": ORANGE, "4c": ORANGE, "5": AQUA}
    xs, dy = 3.3, 0.5
    width_units = xs * (max(depth.values()) + 1) + 0.9
    fig, ax = plt.subplots(figsize=(0.98 * width_units, 0.36 * row + 1.0))
    ax.axis("off")
    ax.set_xlim(-1.2, xs * (max(depth.values()) + 1) - 0.3)
    ax.set_ylim(-(row - 1) * dy - 0.7, 0.75)
    for i, (t, r0, h) in enumerate(bands):
        if i % 2 == 0:
            ax.add_patch(Rectangle((-1.2, -(r0 + h - 1) * dy - dy / 2), 100, h * dy,
                                   color="#f4f3ef", lw=0, zorder=0))
        ax.text(-1.05, -(r0 + (h - 1) / 2) * dy, t, fontsize=15, fontweight="bold",
                color=INK2, va="center")
    w, h = 2.95, 0.38

    def centre(n):
        c, r = pos[n]
        return c * xs + w / 2 - 0.35, -r * dy

    for n in main:
        for u in info[n]["uses"]:
            (x0, y0), (x1, y1) = centre(u), centre(n)
            ax.add_patch(FancyArrowPatch((x0 + w / 2, y0), (x1 - w / 2, y1),
                                         arrowstyle="-|>", mutation_scale=11, lw=0.9,
                                         color=MUTED, alpha=0.8, zorder=1,
                                         connectionstyle="arc3,rad=0.06"))
    for n in main:
        x, y = centre(n)
        col = part_color[info[n]["part"]]
        ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h,
                                    boxstyle="round,pad=0,rounding_size=0.08",
                                    facecolor=tint(col, 0.18),
                                    edgecolor=INK if n in cited else col,
                                    lw=2.2 if n in cited else 1.1, zorder=2))
        ax.text(x, y, n, ha="center", va="center", fontsize=12.5, family="monospace",
                color=INK, zorder=3)
    handles = [plt.Line2D([], [], marker="s", ls="", ms=11, mfc=tint(c, 0.18), mec=c,
                          label=lab)
               for c, lab in [(BLUE, "Part 2: core theorems"),
                              (ORANGE, "Parts 4, 4b, 4c: S, O, W, H0, H, F, M"),
                              (AQUA, "Part 5: A, D, F5 (probability)")]]
    handles.append(plt.Line2D([], [], marker="s", ls="", ms=11, mfc=SURFACE, mec=INK, mew=2.2,
                              label="restated in Part 6 as spec_*"))
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.5, 0.0), ncol=4,
              fontsize=13)
    ax.text(xs * (max(depth.values()) + 1) - 0.4, 0.5, "arrow X → Y: the proof of Y cites X",
            ha="right", fontsize=13, color=INK2)
    save(fig, "fig09_dependencies.png")
    NUM.update(f9_nodes=str(len(main)), f9_edges=str(sum(len(info[n]["uses"]) for n in main)),
               f9_depth=str(max(depth.values())))


def fig10_trust():
    """Trust boundary: what a human reads vs what Lean checks, counted from Kalman.lean."""
    order, info, defs, _ = parse_lean()
    n_def = {p: sum(1 for _, q in defs if q == p) for p in ("1", "3")}
    n_thm = {p: sum(1 for n in order if info[n]["part"] == p)
             for p in ("2", "4", "4b", "4c", "5", "6")}
    fig, ax = plt.subplots(figsize=(12, 5.4))
    ax.axis("off")
    ax.set_xlim(0, 12)
    ax.set_ylim(0, 5.6)
    panels = [(0.2, BLUE, "A human reads and approves",
               [f"Part 1: {n_def['1']} core definitions",
                f"Part 3: {n_def['3']} model definitions",
                f"Part 6: {n_thm['6']} final statements"]),
              (6.4, ORANGE, "Lean's kernel checks",
               [f"Part 2: {n_thm['2']} core proofs",
                f"Part 4: {n_thm['4']} proofs (S, O, W, H0, H)",
                f"Parts 4b, 4c: {n_thm['4b'] + n_thm['4c']} proofs (F, M)",
                f"Part 5: {n_thm['5']} proofs (A, D, F5)"])]
    for x0, col, title, items in panels:
        ax.add_patch(FancyBboxPatch((x0, 1.55), 5.4, 3.75,
                                    boxstyle="round,pad=0,rounding_size=0.18",
                                    facecolor=tint(col, 0.10), edgecolor=col, lw=1.6))
        ax.text(x0 + 0.3, 4.85, title, fontsize=17, fontweight="bold", color=INK, va="center")
        for i, item in enumerate(items):
            yy = 4.15 - i * 0.72
            ax.add_patch(FancyBboxPatch((x0 + 0.3, yy - 0.27), 4.8, 0.54,
                                        boxstyle="round,pad=0,rounding_size=0.1",
                                        facecolor=SURFACE, edgecolor=tint(col, 0.6), lw=1))
            ax.text(x0 + 0.5, yy, item, fontsize=14, color=INK, va="center")
    ax.plot([6.0, 6.0], [1.35, 5.45], color=INK2, lw=1.4, ls=(0, (5, 4)))
    ax.text(6.0, 5.52, "trust boundary", ha="center", fontsize=12, color=INK2)
    ax.add_patch(FancyArrowPatch((6.65, 2.4), (5.55, 2.4), arrowstyle="-|>",
                                 mutation_scale=18, color=INK2, lw=1.4))
    ax.text(6.0, 2.66, "one-line proofs", ha="center", fontsize=10.5, color=INK2,
            bbox=dict(boxstyle="square,pad=0.15", facecolor=SURFACE, edgecolor="none"))
    ax.add_patch(FancyBboxPatch((0.2, 0.15), 11.6, 0.95,
                                boxstyle="round,pad=0,rounding_size=0.12",
                                facecolor="#f4f3ef", edgecolor=AXIS, lw=1))
    ax.text(6.0, 0.62, "Trusted base: the Lean kernel, Mathlib's definitions, and the axioms "
            + ", ".join(AXIOMS), ha="center", va="center", fontsize=13, color=INK)
    save(fig, "fig10_trust.png")
    NUM.update(n_core_defs=str(n_def["1"]), n_model_defs=str(n_def["3"]),
               n_spec=str(n_thm["6"]), n_core_thms=str(n_thm["2"]), n_part4=str(n_thm["4"]),
               n_part4b=str(n_thm["4b"]), n_part4c=str(n_thm["4c"]), n_part5=str(n_thm["5"]),
               n_proved=str(sum(n_thm[p] for p in ("2", "4", "4b", "4c", "5"))))


def burn_in(ratio, eps):
    """Frames until (a²)ⁿ ≤ ε for a = exp(-Δt/τc): n ≥ (τc / 2Δt) ln(1/ε)."""
    return ratio / 2 * np.log(1 / eps)


def fig11_convergence():
    """riccatiIter from five starts converging to steadyVar, under the (a²)ⁿ|P₀ - P∞| bound."""
    tau_c, s2, R = 10.0, 1.0, 0.5         # relaxation time in frames, so a = exp(-1/τc)
    a = float(np.exp(-1.0 / tau_c))
    Q = s2 * (1 - a ** 2)                 # process noise of an OU mode with variance σ2
    Pinf = steady_var(a, Q, R)
    assert abs(riccati_step(a, Q, R, Pinf) - Pinf) < 1e-12      # the fixed point of F
    starts, n, n_left = [0.0, 0.1, 1.0, 2.5, 5.0], 40, 12
    n_burn = int(np.ceil(burn_in(tau_c, 1e-3)))
    steps = np.arange(n + 1)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.6))
    worst = 0.0
    for P0, col in zip(starts, RAMP):
        P = riccati_iter(a, Q, R, P0, n)
        gap, bound = np.abs(P - Pinf), (a ** 2) ** steps * abs(P0 - Pinf)
        worst = max(worst, float(np.max(gap[1:] / bound[1:])))
        ax1.plot(steps[:n_left + 1], P[:n_left + 1], color=col, marker="o", ms=5,
                 mec=SURFACE, mew=1, label=f"{P0:g}")
        keep = gap > 1e-15
        ax2.semilogy(steps[keep], gap[keep], color=col)
        ax2.semilogy(steps, bound, color=col, lw=1.2, ls=(0, (4, 3)))
    ax1.axhline(Pinf, color=INK2, lw=1.2, ls=(0, (4, 3)))
    ax1.text(n_left, Pinf + 0.12, rf"steady state $P_\infty$ = {Pinf:.3f}", ha="right",
             color=INK, fontsize=12)
    ax1.set_xlabel("filter step n")
    ax1.set_ylabel(r"prior variance $P_n$")
    ax1.set_ylim(-0.1, 5.4)
    ax1.legend(title=r"start $P_0$", loc="upper right", title_fontsize=12)
    ax1.set_title("Five starts, one steady state", loc="left", color=INK2, fontsize=12)
    ax2.axvline(n_burn, color=INK2, lw=1.0, ls=(0, (1, 2)))
    ax2.text(n_burn - 0.6, 3e-16, r"burn-in, $\varepsilon = 10^{-3}$", rotation=90,
             ha="right", va="bottom", color=INK2, fontsize=11)
    ax2.plot([], [], color=INK2, label=r"gap $|P_n - P_\infty|$")
    ax2.plot([], [], color=INK2, lw=1.2, ls=(0, (4, 3)),
             label=r"bound $(a^2)^n\,|P_0 - P_\infty|$")
    ax2.set_xlabel("filter step n")
    ax2.set_ylabel("gap (log scale)")
    ax2.set_ylim(1e-16, 30)
    ax2.legend(loc="lower left")
    ax2.set_title(rf"Every gap stays under its bound ($a^2$ = {a ** 2:.3f})", loc="left",
                  color=INK2, fontsize=12)
    fig.tight_layout(w_pad=3)
    save(fig, "fig11_convergence.png")
    NUM.update(f11_tau=f"{tau_c:g}", f11_a=f"{a:.3f}", f11_a2=f"{a ** 2:.3f}",
               f11_Q=f"{Q:.3f}", f11_R=f"{R:g}", f11_s2=f"{s2:g}", f11_Pinf=f"{Pinf:.3f}",
               f11_starts=", ".join(f"{s:g}" for s in starts), f11_worst=f"{worst:.2f}",
               f11_nburn=str(n_burn))


def fig12_burnin():
    """Burn-in frames n ≥ (τc / 2Δt) ln(1/ε) against τc / Δt, for ε = 1e-2 and 1e-3."""
    ratio = np.logspace(0, 3, 300)
    ex = 10.0
    fig, ax = plt.subplots(figsize=(6.4, 4.6))
    for eps, col, k in [(1e-2, BLUE, 2), (1e-3, ORANGE, 3)]:
        ax.loglog(ratio, burn_in(ratio, eps), color=col, label=rf"$\varepsilon = 10^{{-{k}}}$")
        end_dot(ax, ex, burn_in(ex, eps), col)
        NUM[f"f12_n{k}"] = str(int(np.ceil(burn_in(ex, eps))))
        NUM[f"f12_slope{k}"] = f"{np.log(1 / eps) / 2:.2f}"
    ax.text(ex * 1.25, burn_in(ex, 1e-2) * 0.8,
            rf"$\tau_c = 10\,\Delta t$: {NUM['f12_n2']} or {NUM['f12_n3']} frames",
            color=INK, fontsize=12, va="top")
    ax.set_xlabel(r"relaxation time $\tau_c\,/\,\Delta t$ (log scale)")
    ax.set_ylabel("frames to discard (log scale)")
    ax.legend(loc="upper left", title="gap shrunk below", title_fontsize=12)
    ax.set_title(r"Burn-in $n \geq (\tau_c/2\Delta t)\,\ln(1/\varepsilon)$", loc="left",
                 color=INK2, fontsize=12)
    save(fig, "fig12_burnin.png")


def fig13_margin():
    """Detection margin 1 + τ²/S∞ against τ²/S∞, with the observed 4x and noise floors."""
    x = np.logspace(-3, np.log10(6), 400)
    fig, ax = plt.subplots(figsize=(6.4, 4.6))
    ax.semilogx(x, 1 + x, color=BLUE)
    end_dot(ax, 3.0, 4.0, BLUE)
    ax.annotate("observed 4x:\n" + r"$\tau^2/S_\infty = 3$", xy=(3.0, 4.0), xytext=(0.18, 4.3),
                color=INK, fontsize=12, va="center",
                arrowprops=dict(arrowstyle="-", color=INK2, lw=1))
    for N, ls, k in [(1_000, (0, (4, 3)), "1e3"), (100_000, (0, (1, 2)), "1e5")]:
        thr = 3 * np.sqrt(2 / N)
        ax.axvline(thr, color=INK2, lw=1.2, ls=ls)
        ax.text(thr * 0.88, 6.3, f"noise floor, N = {N:,}", rotation=90, ha="right",
                va="top", color=INK2, fontsize=11)
        NUM[f"f13_thr_{k}"] = f"{thr:.2g}"
    ax.set_xlabel(r"omitted variance / expected, $\tau^2/S_\infty$ (log scale)")
    ax.set_ylabel(r"innovation variance / $S_\infty$")
    ax.set_ylim(0.6, 6.5)
    ax.set_title(r"Margin $1 + \tau^2/S_\infty$ (F5) vs noise", loc="left", color=INK2,
                 fontsize=12)
    save(fig, "fig13_margin.png")


def fig14_stationary():
    """Numeric check of M2: a 3-basin generator built from jumpRate keeps p stationary."""
    rng = np.random.default_rng(14)
    p = np.array([0.5, 0.3, 0.2])
    kappa = rng.uniform(0.5, 2.0, (3, 3))
    kappa = (kappa + kappa.T) / 2                 # symmetric prefactors, κij = κji
    L = generator(kappa, p)
    max_res = float(np.max(np.abs(p @ L)))        # pᵀL: zero up to rounding (M2)
    outflow = -np.diag(L)
    jumps = 200_000
    u, w = rng.random(jumps), rng.exponential(1.0, jumps)
    others = [[j for j in range(3) if j != i] for i in range(3)]
    first = [L[i, others[i][0]] / outflow[i] for i in range(3)]
    occ, state = np.zeros(3), 0
    for k in range(jumps):                        # continuous-time chain with generator L
        occ[state] += w[k] / outflow[state]
        state = others[state][0] if u[k] < first[state] else others[state][1]
    occ /= occ.sum()
    xs = np.arange(1, 4)
    fig, ax = plt.subplots(figsize=(10, 4.4))
    for dx, vals, col, lab in [(-0.19, p, BLUE, "target population $p_j$"),
                               (0.19, occ, ORANGE, "simulated occupancy")]:
        ax.bar(xs + dx, vals, width=0.34, color=col, lw=0, zorder=3, label=lab)
        for xv, v in zip(xs + dx, vals):
            ax.text(xv, v + 0.012, f"{v:.3f}", ha="center", va="bottom", color=INK, fontsize=12)
    ax.set_xticks(xs, [f"basin {k}" for k in xs])
    ax.set_ylabel("fraction of time")
    ax.set_ylim(0, 0.62)
    ax.legend(loc="upper right")
    res_txt = "0 exactly" if max_res == 0 else f"{max_res:.0e}"
    ax.set_title(rf"Largest entry of $|p^\top L|$: {res_txt}; {jumps:,} simulated jumps",
                 loc="left", color=INK2, fontsize=12)
    save(fig, "fig14_stationary.png")
    NUM.update(f14_p=", ".join(f"{v:g}" for v in p), f14_maxres=res_txt,
               f14_jumps=f"{jumps:,}", f14_occ=", ".join(f"{v:.3f}" for v in occ),
               f14_occ_err=f"{np.max(np.abs(occ - p)):.3f}")


def main():
    FIG.mkdir(exist_ok=True)
    setup_style()
    for make in (fig01_fusion, fig02_parabola, fig03_ratio, fig04_sensors, fig05_ou,
                 fig06_innovations, fig07_autocorr, fig08_msm, fig09_dependencies,
                 fig10_trust, fig11_convergence, fig12_burnin, fig13_margin,
                 fig14_stationary):
        make()
    js = "// Generated by make_figures.py: every number quoted on the slides.\n"
    js += "window.KF = " + json.dumps(NUM, indent=1, ensure_ascii=False, sort_keys=True) + ";\n"
    (FIG / "numbers.js").write_text(js, encoding="utf-8")
    print("wrote", FIG / "numbers.js")
    for k in sorted(NUM):
        print(f"  {k} = {NUM[k]}")


if __name__ == "__main__":
    main()
