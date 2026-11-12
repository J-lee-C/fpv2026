"""Make every figure, number and Lean excerpt used by kalman_writeup.tex.

    python make_writeup_figures.py              # everything
    python make_writeup_figures.py bayes ou     # only the named figures (plus the excerpts)

Writes figures/*.pdf (diagrams, plots) and figures/*.png (3D renderings), generated/numbers.tex
(every number the text quotes), generated/lean/*.lean (verbatim excerpts of ../Kalman.lean) and
generated/lean_unicode.tex (how the excerpts' non-ASCII characters are typeset). Fixed seeds;
numpy and matplotlib only. The Lean definitions are transcribed once, in
../presentation/make_figures.py, and imported from there.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "presentation"))
import make_figures as deck  # noqa: E402  (also selects the Agg backend)

import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.colors import LightSource, to_rgb  # noqa: E402
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch  # noqa: E402
from mpl_toolkits.mplot3d import proj3d  # noqa: E402
from mpl_toolkits.mplot3d.art3d import Line3DCollection, Poly3DCollection  # noqa: E402

FIG, GEN = HERE / "figures", HERE / "generated"
LEAN = HERE.parent / "Kalman.lean"

INK, INK2, MUTED, GRID, AXIS = deck.INK, deck.INK2, deck.MUTED, deck.GRID, deck.AXIS
BLUE, ORANGE, AQUA, RAMP = deck.BLUE, deck.ORANGE, deck.AQUA, deck.RAMP
BASIN = [BLUE, ORANGE, AQUA]          # basins A, B, C keep these colors everywhere
NAMES = ["A", "B", "C"]
WASH = "#f3f2ee"                      # light neutral panel
NUM: dict[str, str] = {}
BOLD = dict(family="cmb10")


def setup_style():
    plt.rcParams.update({
        "figure.facecolor": "white", "axes.facecolor": "white", "savefig.facecolor": "white",
        "font.family": "serif", "font.serif": ["cmr10"], "font.monospace": ["cmtt10"],
        "mathtext.fontset": "cm", "axes.unicode_minus": False,
        "axes.formatter.use_mathtext": True,
        "font.size": 9, "axes.titlesize": 9.5, "axes.labelsize": 9,
        "xtick.labelsize": 8, "ytick.labelsize": 8, "legend.fontsize": 8,
        "legend.frameon": False, "axes.edgecolor": AXIS, "axes.linewidth": 0.6,
        "axes.labelcolor": INK2, "axes.spines.top": False, "axes.spines.right": False,
        "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.5, "axes.axisbelow": True,
        "xtick.color": AXIS, "ytick.color": AXIS, "xtick.labelcolor": INK2,
        "ytick.labelcolor": INK2, "lines.linewidth": 1.4, "lines.solid_capstyle": "round",
        "text.color": INK, "pdf.fonttype": 42,
    })


def save(fig, name, tight=True):
    """Save at 300 dpi; 3D renderings keep their canvas (tight=False); PNGs are then cropped."""
    fig.savefig(FIG / name, dpi=300, bbox_inches="tight" if tight else None,
                pad_inches=0.03)
    plt.close(fig)
    if name.endswith(".png"):
        autocrop(FIG / name)
    print("wrote", FIG / name)


def autocrop(path, pad=24):
    """Trim the white margins a 3D canvas leaves around its content (pad in pixels)."""
    img = plt.imread(path)
    ink = (img[..., :3] < 0.985).any(axis=-1)
    ys, xs = np.nonzero(ink)
    y0, y1 = max(ys.min() - pad, 0), min(ys.max() + pad + 1, img.shape[0])
    x0, x1 = max(xs.min() - pad, 0), min(xs.max() + pad + 1, img.shape[1])
    plt.imsave(path, img[y0:y1, x0:x1])


def tint(color, t):
    """`t` of the way from white to `color`, as an RGB triple."""
    c = np.array(to_rgb(color))
    return tuple(1 - t * (1 - c))


def fmt(x, digits=3):
    return f"{x:.{digits}f}"


# ----------------------------------------------------------------------------------------
# Verbatim Lean excerpts.
def lean_blocks():
    """Name -> text of each def/theorem in Kalman.lean (its comment lines, docstring, code)."""
    blocks = {}
    for chunk in re.split(r"\n[ \t]*\n", LEAN.read_text(encoding="utf-8")):
        m = re.search(r"(?m)^(?:def|theorem) (\w+)", chunk)
        if m and not chunk.lstrip().startswith("/-!"):
            assert chunk.lstrip().startswith(("/--", "--")), chunk[:60]
            blocks[m.group(1)] = chunk.strip("\n")
    return blocks


def statement_only(block):
    """Drop the one-line proof of a Part 6 theorem, keeping everything before `:=`."""
    lines = block.split("\n")
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].rstrip().endswith(":="):
            return "\n".join(lines[:i] + [lines[i].rstrip()[:-2].rstrip()])
    raise ValueError(block)


DEFS = ["postVar", "gain", "optVar", "updErr", "ouPredict", "ouRiccati", "innovCov", "msm",
        "switchCov", "riccatiStep", "riccatiIter", "steadyVar", "jumpRate", "generator"]
PROOFS = ["complete_square", "gain_optimal", "gain_unique", "optVar_le", "white_iff",
          "detailed_balance", "populations_stationary", "steadyVar_fixed", "riccati_tendsto",
          "variance_update"]

# How each non-ASCII character of the excerpts is typeset, with its rough width in em.
UNICODE = {
    "ℝ": (r"\ensuremath{\mathbb{R}}", 0.72), "ℕ": (r"\ensuremath{\mathbb{N}}", 0.72),
    "→": (r"\ensuremath{\to}", 1.0), "←": (r"\ensuremath{\leftarrow}", 1.0),
    "↔": (r"\ensuremath{\leftrightarrow}", 1.0), "∀": (r"\ensuremath{\forall}", 0.56),
    "∃": (r"\ensuremath{\exists}", 0.56), "∑": (r"\ensuremath{\textstyle\sum}", 1.0),
    "∈": (r"\ensuremath{\in}", 0.67), "≤": (r"\ensuremath{\le}", 0.78),
    "≥": (r"\ensuremath{\ge}", 0.78), "≠": (r"\ensuremath{\ne}", 0.78),
    "∧": (r"\ensuremath{\land}", 0.67), "∨": (r"\ensuremath{\lor}", 0.67),
    "¬": (r"\ensuremath{\lnot}", 0.67), "⟨": (r"\ensuremath{\langle}", 0.39),
    "⟩": (r"\ensuremath{\rangle}", 0.39), "·": (r"\ensuremath{\cdot}", 0.5),
    "•": (r"\ensuremath{\bullet}", 0.5), "×": (r"\ensuremath{\times}", 0.78),
    "⟂": (r"\ensuremath{\perp}", 0.78), "√": (r"\ensuremath{\surd}", 0.83),
    "²": (r"\ensuremath{^{2}}", 0.35), "¹": (r"\ensuremath{^{1}}", 0.35),
    "⁻": (r"\ensuremath{^{-}}", 0.5), "ⁿ": (r"\ensuremath{^{n}}", 0.4),
    "ᵀ": (r"\ensuremath{^{\mathsf{T}}}", 0.4),
    "₀": (r"\ensuremath{_{0}}", 0.35), "₁": (r"\ensuremath{_{1}}", 0.35),
    "₂": (r"\ensuremath{_{2}}", 0.35), "ᵢ": (r"\ensuremath{_{i}}", 0.3),
    "ⱼ": (r"\ensuremath{_{j}}", 0.3), "𝓝": (r"\ensuremath{\mathcal{N}}", 0.8),
    "α": (r"\ensuremath{\alpha}", 0.64), "β": (r"\ensuremath{\beta}", 0.57),
    "κ": (r"\ensuremath{\kappa}", 0.58), "λ": (r"\ensuremath{\lambda}", 0.58),
    "μ": (r"\ensuremath{\mu}", 0.6), "σ": (r"\ensuremath{\sigma}", 0.57),
    "τ": (r"\ensuremath{\tau}", 0.44), "ω": (r"\ensuremath{\omega}", 0.62),
    "Ω": (r"\ensuremath{\Omega}", 0.72), "ε": (r"\ensuremath{\varepsilon}", 0.47),
    "ν": (r"\ensuremath{\nu}", 0.5), "φ": (r"\ensuremath{\varphi}", 0.65),
}
CODE_PT, CODE_LIMIT_PT = 8.0, 452.0   # code font size; usable width inside a code box


def write_lean_excerpts():
    blocks = lean_blocks()
    out = GEN / "lean"
    out.mkdir(parents=True, exist_ok=True)
    texts = {n: blocks[n] for n in DEFS + PROOFS}
    specs = [n for n in blocks if n.startswith("spec_")]
    assert len(specs) == 17, specs
    texts.update({n: statement_only(blocks[n]) for n in specs})
    used, widest = set(), (0.0, "")
    for name, text in texts.items():
        (out / f"{name}.lean").write_text(text + "\n", encoding="utf-8")
        for line in text.split("\n"):
            used.update(ch for ch in line if ord(ch) > 127)
            em = sum(UNICODE[ch][1] if ord(ch) > 127 else 0.525 for ch in line)
            widest = max(widest, (em * CODE_PT, f"{name}: {line.strip()[:50]}"))
    missing = sorted(used - UNICODE.keys())
    assert not missing, f"no typesetting rule for {missing}"
    lines = ["% Generated by make_writeup_figures.py: how the Lean excerpts' non-ASCII",
             "% characters are typeset (loaded by kalman_writeup.tex)."]
    lines += [rf"\newunicodechar{{{ch}}}{{{UNICODE[ch][0]}}}" for ch in sorted(used)]
    (GEN / "lean_unicode.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {len(texts)} Lean excerpts; widest line {widest[0]:.0f}pt ({widest[1]})")
    assert widest[0] <= CODE_LIMIT_PT, "a code line is too wide for the code box"
    NUM.update(nSpec=str(len(specs)), nDefsCore="3", nDefsModel=str(len(DEFS) - 3))


# ----------------------------------------------------------------------------------------
# The running example: a molecule-like point moving in a three-basin energy landscape.
WELLS = [((-1.25, -0.55), 3.07, 0.72),    # basin A: center, depth, width
         ((1.25, -0.45), 2.78, 0.68),     # basin B
         ((0.05, 1.30), 2.51, 0.66)]      # basin C
THETA = 0.5                               # noise strength ("temperature")
CONF = 0.035                              # quartic confinement


def energy(x, y):
    v = CONF * (x ** 2 + y ** 2) ** 2
    for (cx, cy), depth, w in WELLS:
        v = v - depth * np.exp(-((x - cx) ** 2 + (y - cy) ** 2) / (2 * w * w))
    return v


def grad(x, y):
    r2 = x ** 2 + y ** 2
    gx, gy = 4 * CONF * r2 * x, 4 * CONF * r2 * y
    for (cx, cy), depth, w in WELLS:
        g = depth * np.exp(-((x - cx) ** 2 + (y - cy) ** 2) / (2 * w * w)) / (w * w)
        gx, gy = gx + g * (x - cx), gy + g * (y - cy)
    return gx, gy


def descend(x, y, steps=4000, h=0.01):
    """Follow -grad V (plain gradient descent) from many points at once."""
    x, y = np.array(x, float), np.array(y, float)
    for _ in range(steps):
        gx, gy = grad(x, y)
        x, y = x - h * gx, y - h * gy
    return x, y


class Landscape:
    """Minima, basin map, populations and a simulated run, computed once and cached."""

    def __init__(self):
        mx, my = descend([c[0] for c, _, _ in WELLS], [c[1] for c, _, _ in WELLS])
        self.minima = np.stack([mx, my], axis=1)
        self.lim = 2.5
        g = np.linspace(-self.lim, self.lim, 241)
        self.step = g[1] - g[0]
        self.gx, self.gy = np.meshgrid(g, g)
        self.V = energy(self.gx, self.gy)
        self.label = self.basin_of(self.gx, self.gy)
        w = np.exp(-(self.V - self.V.min()) / THETA)
        self.density = w / (w.sum() * self.step ** 2)
        self.pop = np.array([w[self.label == i].sum() for i in range(3)]) / w.sum()
        self._run = None

    def path(self, steps=7000, every=2, dt=0.004, hops=(2, 3)):
        """One walker at fine time resolution whose path visits all three basins."""
        sd = np.sqrt(2 * THETA * dt)
        for seed in range(100, 300):
            rng = np.random.default_rng(seed)
            noise = sd * rng.standard_normal((steps, 2))
            x, y = self.minima[0]
            xs, ys = np.empty(steps // every), np.empty(steps // every)
            for k in range(steps):
                gx, gy = grad(x, y)
                x, y = x - gx * dt + noise[k, 0], y - gy * dt + noise[k, 1]
                if k % every == every - 1:
                    xs[k // every], ys[k // every] = x, y
            core = self.core_labels(xs[:, None], ys[:, None])[:, 0]
            n_hops = int((core[1:] != core[:-1]).sum())
            if (core >= 0).all() and len(set(core.tolist())) == 3 and \
                    hops[0] <= n_hops <= hops[1]:
                return xs, ys, core
        raise RuntimeError("no seed gives a path through all three basins")

    def basin_of(self, x, y):
        """Which minimum plain downhill motion from (x, y) ends at."""
        ex, ey = descend(x, y, steps=1500, h=0.02)
        d = [(ex - mx) ** 2 + (ey - my) ** 2 for mx, my in self.minima]
        return np.argmin(np.stack(d), axis=0)

    def run(self):
        """Overdamped Langevin walkers x <- x - grad V dt + sqrt(2 theta dt) xi (seed 1)."""
        if self._run is None:
            rng = np.random.default_rng(1)
            walkers, steps, dt, every = 40, 125_000, 0.004, 20
            start = rng.integers(0, 3, walkers)
            x, y = self.minima[start, 0].copy(), self.minima[start, 1].copy()
            frames = steps // every
            X, Y = np.empty((frames, walkers)), np.empty((frames, walkers))
            sd = np.sqrt(2 * THETA * dt)
            for k in range(steps):
                gx, gy = grad(x, y)
                x = x - gx * dt + sd * rng.standard_normal(walkers)
                y = y - gy * dt + sd * rng.standard_normal(walkers)
                if k % every == every - 1:
                    X[k // every], Y[k // every] = x, y
            self._run = dict(X=X, Y=Y, dt=dt * every)
            self._run["basin"] = self.lookup(X, Y)
            self._run["core"] = self.core_labels(X, Y)
        return self._run

    def lookup(self, X, Y):
        """Basin label of each sample, read off the precomputed basin map."""
        n = self.gx.shape[0]
        i = np.clip(np.rint((Y + self.lim) / (2 * self.lim) * (n - 1)).astype(int), 0, n - 1)
        j = np.clip(np.rint((X + self.lim) / (2 * self.lim) * (n - 1)).astype(int), 0, n - 1)
        return self.label[i, j]

    def core_labels(self, X, Y, radius=0.45):
        """Label = the last basin core (disc around a minimum) visited: no recrossing noise."""
        lab = np.full(X.shape, -1)
        for b, (mx, my) in enumerate(self.minima):
            lab[(X - mx) ** 2 + (Y - my) ** 2 < radius ** 2] = b
        for t in range(1, lab.shape[0]):
            keep = lab[t] < 0
            lab[t, keep] = lab[t - 1, keep]
        return lab


_LAND = None


def land():
    global _LAND
    if _LAND is None:
        _LAND = Landscape()
    return _LAND


def saddles(L):
    """Lowest point on the border between each pair of basins: the mountain passes."""
    out = {}
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        border = np.zeros(L.label.shape, bool)
        for shift in [(0, 1), (1, 0)]:
            nb = np.roll(L.label, shift, axis=(0, 1))
            border |= ((L.label == i) & (nb == j)) | ((L.label == j) & (nb == i))
        k = int(np.argmin(np.where(border, L.V, np.inf)))
        out[(i, j)] = (L.gx.flat[k], L.gy.flat[k], L.V.flat[k])
    return out


def fit_surrogate(L):
    """Read the surrogate's parameters off the simulated run (frame units)."""
    r = L.run()
    X, core, basin = r["X"], r["core"], r["basin"]
    trans = np.zeros((3, 3))
    for w in range(core.shape[1]):
        c = core[:, w][core[:, w] >= 0]
        moved = c[:-1] != c[1:]
        np.add.at(trans, (c[:-1][moved], c[1:][moved]), 1)
    frames = np.array([(core == i).sum() for i in range(3)], float)
    mu, s2, a = [], [], []
    for i in range(3):
        inside = (core == i) & (basin == i)
        mu.append(X[inside].mean())
        s2.append(X[inside].var())
        both = inside[:-1] & inside[1:]
        x0, x1 = X[:-1][both] - mu[-1], X[1:][both] - mu[-1]
        a.append(float((x0 * x1).mean() / (x0 * x0).mean()))
    return dict(p=frames / frames.sum(), k=trans / frames[:, None], trans=trans,
                mu=np.array(mu), s2=np.array(s2), a=np.array(a), dt=r["dt"])


def simulate_surrogate(fit, n, rng, start=0):
    """Switching OU: label jumps with the fitted per-frame rates; x is OU inside a basin."""
    s, x = np.empty(n, int), np.empty(n)
    s[0], x[0] = start, fit["mu"][start]
    for t in range(1, n):
        i = s[t - 1]
        out = fit["k"][i].copy()
        out[i] = 0.0
        u = rng.random()
        if u < out.sum():
            j = int(np.searchsorted(np.cumsum(out), u, side="right"))
            s[t] = j
            x[t] = fit["mu"][j] + np.sqrt(fit["s2"][j]) * rng.standard_normal()
        else:
            s[t] = i
            a, mu, v = fit["a"][i], fit["mu"][i], fit["s2"][i]
            x[t] = mu + a * (x[t - 1] - mu) + np.sqrt(v * (1 - a * a)) * rng.standard_normal()
    return s, x


def view_vector(elev, azim):
    e, a = np.radians(elev), np.radians(azim)
    return np.array([np.cos(e) * np.cos(a), np.cos(e) * np.sin(a), np.sin(e)])


def unit(v):
    return v / np.linalg.norm(v, axis=-1, keepdims=True)


def phong(normals, base, view, light, amb=0.36, dif=0.62, spec=0.38, shine=28):
    """Per-vertex Phong shading: ambient + diffuse + a white specular highlight."""
    n = unit(normals)
    ndl = np.clip((n * light).sum(-1), 0, 1)
    refl = 2 * ndl[..., None] * n - light
    rdv = np.clip((refl * view).sum(-1), 0, 1)
    col = np.array(to_rgb(base)) * (amb + dif * ndl)[..., None]
    return np.clip(col + spec * (rdv ** shine)[..., None], 0, 1)


def sphere(ax, c, r, color, view, light, z):
    u, v = np.meshgrid(np.linspace(0, 2 * np.pi, 72), np.linspace(0, np.pi, 36))
    n = np.stack([np.cos(u) * np.sin(v), np.sin(u) * np.sin(v), np.cos(v)], axis=-1)
    P = c + r * n
    ax.plot_surface(P[..., 0], P[..., 1], P[..., 2], facecolors=phong(n, color, view, light),
                    rstride=1, cstride=1, linewidth=0, antialiased=False, shade=False,
                    zorder=z)


def cylinder(ax, p, q, r, color, view, light, z):
    axis = unit(q - p)
    e1 = unit(np.cross(axis, [0.31, 0.57, 0.76]))
    e2 = np.cross(axis, e1)
    t, s = np.meshgrid(np.linspace(0, 2 * np.pi, 28), np.linspace(0, 1, 2))
    n = np.cos(t)[..., None] * e1 + np.sin(t)[..., None] * e2
    P = p + s[..., None] * (q - p) + r * n
    ax.plot_surface(P[..., 0], P[..., 1], P[..., 2], facecolors=phong(n, color, view, light),
                    rstride=1, cstride=1, linewidth=0, antialiased=False, shade=False,
                    zorder=z)


def clean_3d(ax):
    ax.set_axis_off()
    ax.computed_zorder = False


def fig_molecule():
    """Four atoms, three bonds, and the torsion angle phi between the two planes."""
    b, bond_angle, phi = 1.5, np.radians(111.0), np.radians(62.0)
    p2, p3 = np.zeros(3), np.array([b, 0.0, 0.0])
    p1 = p2 + b * np.array([np.cos(bond_angle), np.sin(bond_angle), 0.0])
    s = np.sin(np.pi - bond_angle)
    p4 = p3 + b * np.array([-np.cos(bond_angle), s * np.cos(phi), s * np.sin(phi)])
    atoms = [p1, p2, p3, p4]
    elev, azim = 22, -36
    view = view_vector(elev, azim)
    light = unit(view + np.array([-0.35, 0.25, 0.95]))
    fig = plt.figure(figsize=(3.4, 2.5))
    ax = fig.add_axes([-0.1, -0.16, 1.2, 1.3], projection="3d")
    clean_3d(ax)
    ax.view_init(elev, azim)
    ax.set_proj_type("persp", focal_length=2.4)
    u = unit(p3 - p2)
    d1, d4 = unit(p1 - p2 - ((p1 - p2) @ u) * u), unit(p4 - p3 - ((p4 - p3) @ u) * u)
    for tri, col in [((p1, p2, p3), BLUE), ((p2, p3, p4), ORANGE)]:
        ax.add_collection3d(Poly3DCollection([np.array(tri)], facecolor=tint(col, 0.6),
                                             alpha=0.5, edgecolor=col, linewidth=0.9,
                                             zorder=1))
    depth = [a @ view for a in atoms]
    order = np.argsort(depth)
    for k, (i, j) in enumerate(sorted([(0, 1), (1, 2), (2, 3)],
                                      key=lambda e: (atoms[e[0]] + atoms[e[1]]) @ view)):
        cylinder(ax, atoms[i], atoms[j], 0.07, "#a9a7a0", view, light, z=2 + k)
    for k, i in enumerate(order):
        sphere(ax, atoms[i], 0.27, "#a7a59e" if i in (0, 3) else "#7a7872", view, light,
               z=6 + k)
    m = (p2 + p3) / 2
    rho = 0.8
    t = np.linspace(0, phi, 60)
    perp = np.cross(u, d1)
    arc = m + rho * (np.cos(t)[:, None] * d1 + np.sin(t)[:, None] * perp)
    for d in (d1, d4):
        ax.plot(*np.stack([m, m + 1.2 * rho * d]).T, color=INK, lw=0.8, ls=(0, (3, 2)),
                zorder=20)
    ax.plot(*arc.T, color=INK, lw=1.3, zorder=21)
    mid = m + 1.4 * rho * (np.cos(phi / 2) * d1 + np.sin(phi / 2) * perp)
    ax.text(*mid, r"$\varphi$", fontsize=13, color=INK, zorder=22, ha="center", va="center")
    for i, a in enumerate(atoms):
        off = {0: [-0.1, 0.2, 0.42], 1: [-0.2, -0.15, -0.45], 2: [0.25, -0.15, -0.45],
               3: [0.12, 0.08, 0.42]}[i]
        ax.text(*(a + off), str(i + 1), fontsize=10, color=INK, zorder=23, ha="center",
                va="center", **BOLD)
    pts = np.array(atoms)
    c, half = pts.mean(0), 1.2
    ax.set_xlim(c[0] - half, c[0] + half)
    ax.set_ylim(c[1] - half, c[1] + half)
    ax.set_zlim(c[2] - half, c[2] + half)
    ax.set_box_aspect((1, 1, 1))
    save(fig, "molecule.png", tight=False)
    NUM.update(molPhi=f"{np.degrees(phi):.0f}")


def softcap(v, top=1.1):
    """Flatten the high plateau of the landscape so the valleys dominate the picture."""
    return np.where(v > 0, top * np.tanh(v / top), v)


def basin_surface_colors(lab, Z, zmax):
    t = np.clip((zmax - Z) / (zmax - Z.min()), 0, 1)
    rgb = np.empty(Z.shape + (3,))
    for i, col in enumerate(BASIN):
        m = lab == i
        c = np.array(to_rgb(col))
        rgb[m] = 1 - (0.16 + 0.66 * t[m])[:, None] * (1 - c)
    return rgb


def fig_landscape():
    """The energy landscape in 3D, basins colored, with a simulated path on it."""
    L, r = land(), land().run()
    X, Y, V, lab = L.gx, L.gy, L.V, L.label
    Z = softcap(V)
    ls = LightSource(azdeg=305, altdeg=38)
    rgb = ls.shade_rgb(basin_surface_colors(lab, Z, Z.max()), Z, blend_mode="soft",
                       fraction=0.9, vert_exag=1.6, dx=L.step, dy=L.step)
    fig = plt.figure(figsize=(6.4, 3.7))
    ax = fig.add_axes([-0.06, -0.24, 1.12, 1.32], projection="3d")
    clean_3d(ax)
    elev, azim = 38, -63
    ax.view_init(elev, azim)
    ax.set_proj_type("persp", focal_length=1.8)
    floor = Z.min() - 0.3
    ax.contour(X, Y, V, levels=np.linspace(-2.7, -0.3, 9), zdir="z", offset=floor,
               colors=[GRID], linewidths=0.5, linestyles="solid", zorder=0)
    ax.plot_surface(X, Y, Z, facecolors=rgb, rstride=1, cstride=1, linewidth=0,
                    antialiased=False, shade=False, zorder=1)
    xs, ys, cs = L.path()
    zs = softcap(energy(xs, ys)) + 0.04
    pts = np.stack([xs, ys, zs], axis=1)
    segs = np.stack([pts[:-1], pts[1:]], axis=1)
    dark = [tuple(0.5 * np.array(to_rgb(BASIN[c]))) for c in cs[:-1]]
    ax.add_collection3d(Line3DCollection(segs, colors=dark, linewidths=0.32, alpha=0.6,
                                         zorder=5))
    ax.scatter(*pts[0], s=14, color=INK, edgecolor="white", linewidths=0.6, zorder=6,
               depthshade=False)
    for i, (mx, my) in enumerate(L.minima):
        ax.text(mx, my, energy(mx, my) + 1.35, f"basin {NAMES[i]}", fontsize=10, ha="center",
                color=INK, zorder=8, **BOLD)
        ax.plot([mx, mx], [my, my], [energy(mx, my) + 0.12, energy(mx, my) + 1.2],
                color=INK2, lw=0.6, zorder=7)
    sad = saddles(L)
    for sx, sy, sv in sad.values():
        ax.scatter([sx], [sy], [softcap(sv) + 0.06], s=16, color="white", edgecolor=INK,
                   linewidths=0.7, zorder=9, depthshade=False)
    ax.set_xlim(-L.lim, L.lim)
    ax.set_ylim(-L.lim, L.lim)
    ax.set_zlim(floor, Z.max())
    ax.set_box_aspect((1, 1, 0.55))
    save(fig, "landscape.png", tight=False)
    vmin = energy(L.minima[:, 0], L.minima[:, 1])
    barriers = [v - vmin[i] for (i, j), (_, _, v) in sad.items()]
    barriers += [v - vmin[j] for (i, j), (_, _, v) in sad.items()]
    NUM.update(theta=f"{THETA:g}", barrierLow=fmt(min(barriers), 1),
               barrierHigh=fmt(max(barriers), 1), walkers=str(r["X"].shape[1]),
               frames=f"{r['X'].shape[0]:,}", frameDt=f"{r['dt']:g}")


def colored_series(ax, t, x, lab, lw=0.7):
    from matplotlib.collections import LineCollection
    pts = np.stack([t, x], axis=1)
    segs = np.stack([pts[:-1], pts[1:]], axis=1)
    cols = [tuple(0.8 * np.array(to_rgb(BASIN[c]))) for c in lab[:-1]]
    ax.add_collection(LineCollection(segs, colors=cols, linewidths=lw))
    edges = np.flatnonzero(np.diff(lab)) + 1
    for a, b in zip(np.r_[0, edges], np.r_[edges, len(lab)]):
        ax.axvspan(t[a], t[min(b, len(t) - 1)], color=tint(BASIN[lab[a]], 0.12), lw=0,
                   zorder=0)


def fig_timescales():
    """MD-like run vs the fitted switching surrogate: fast rattle, rare hops."""
    L, r = land(), land().run()
    fit = fit_surrogate(L)
    n, w = 1500, 0
    core = r["core"][:, w]
    t0 = int(np.argmax(core >= 0))
    lab, x = core[t0:t0 + n], r["X"][t0:t0 + n, w]
    t = np.arange(n) * r["dt"]
    s, z = simulate_surrogate(fit, n, np.random.default_rng(3), start=int(lab[0]))
    fig, (a1, a2) = plt.subplots(2, 1, figsize=(6.4, 3.3), sharex=True)
    panels = [(a1, x, lab, "(a) Simulated motion in the landscape (downhill plus random kicks)"),
              (a2, z, s, "(b) The surrogate: the hidden label jumps; OU motion inside a basin")]
    for ax, xx, ll, title in panels:
        colored_series(ax, t, xx, ll)
        ax.set_xlim(t[0], t[-1])
        ax.set_ylim(-2.3, 2.3)
        ax.set_ylabel("coordinate $x_1$")
        ax.set_title(title, loc="left", color=INK2, fontsize=9)
        ax.grid(False)
        for i, mu in enumerate(fit["mu"]):
            ax.text(t[-1] + 1.2, mu, NAMES[i], color=INK, fontsize=9, va="center", **BOLD)
    a2.set_xlabel("time")
    fig.tight_layout(h_pad=0.6)
    save(fig, "timescales.pdf")
    hops = (np.diff(r["core"], axis=0) != 0) & (r["core"][:-1] >= 0)
    dwell = (r["core"] >= 0).sum() / max(hops.sum(), 1) * r["dt"]
    NUM.update(dwell=f"{dwell:.1f}", relax=fmt(-r["dt"] / np.log(fit["a"].mean()), 2),
               hops=f"{int(hops.sum()):,}")
    p, k = fit["p"], fit["k"]
    flows = {(i, j): (p[i] * k[i, j], p[j] * k[j, i]) for i, j in [(0, 1), (0, 2), (1, 2)]}
    asym = max(abs(f - g) / ((f + g) / 2) for f, g in flows.values())
    NUM.update(fitAsym=f"{100 * asym:.0f}", fitTrans=f"{int(fit['trans'].sum()):,}")
    for (i, j), (f, g) in flows.items():
        NUM[f"flow{NAMES[i]}{NAMES[j]}"] = f"{1000 * f:.2f}"
        NUM[f"flow{NAMES[j]}{NAMES[i]}"] = f"{1000 * g:.2f}"
    for i in range(3):
        NUM[f"occ{NAMES[i]}"] = fmt(p[i], 2)


def fig_density():
    """Equilibrium density exp(-V/theta)/Z in 3D, and basin populations vs time spent."""
    L, r = land(), land().run()
    X, Y, D, lab = L.gx, L.gy, L.density, L.label
    ls = LightSource(azdeg=305, altdeg=40)
    rgb = ls.shade_rgb(basin_surface_colors(lab, -D, 0.0), D, blend_mode="soft",
                       fraction=0.7, vert_exag=0.9, dx=L.step, dy=L.step)
    fig = plt.figure(figsize=(6.4, 2.6))
    ax = fig.add_axes([-0.08, -0.22, 0.76, 1.42], projection="3d")
    clean_3d(ax)
    ax.view_init(30, -63)
    ax.set_proj_type("persp", focal_length=1.8)
    ax.plot_surface(X, Y, D, facecolors=rgb, rstride=1, cstride=1, linewidth=0,
                    antialiased=False, shade=False, zorder=1)
    lift = {0: (0.0, 0.0, 0.08, "center"), 1: (1.1, -0.2, 0.05, "left"),
            2: (-0.8, 0.5, 0.32, "center")}
    for i in range(3):
        k = np.unravel_index(np.argmax(np.where(lab == i, D, -1)), D.shape)
        dx, dy, dz, ha = lift[i]
        top = (X[k] + dx, Y[k] + dy, D[k] + dz * D.max())
        ax.plot([X[k], top[0]], [Y[k], top[1]], [D[k], top[2]], color=INK2, lw=0.6, zorder=7)
        ax.text(*top, rf" $p_{NAMES[i]} = {L.pop[i]:.2f}$ ", fontsize=9.5, ha=ha,
                va="bottom", color=INK, zorder=8)
    ax.set_box_aspect((1, 1, 0.5))
    ax.set_xlim(-L.lim, L.lim)
    ax.set_ylim(-L.lim, L.lim)
    ax.set_zlim(0, D.max() * 1.1)
    occ = np.array([(r["basin"] == i).mean() for i in range(3)])
    bx = fig.add_axes([0.71, 0.17, 0.28, 0.62])
    xs = np.arange(3)
    bx.bar(xs - 0.19, L.pop, width=0.34, color=[tint(c, 0.95) for c in BASIN], lw=0,
           zorder=3, label=r"area under $\pi$ (exact)")
    bx.bar(xs + 0.19, occ, width=0.34, color=[tint(c, 0.4) for c in BASIN], lw=0, zorder=3,
           label="fraction of time in the run")
    for xv, v in zip(np.r_[xs - 0.19, xs + 0.19], np.r_[L.pop, occ]):
        bx.text(xv, v + 0.012, f"{v:.2f}", ha="center", fontsize=7.5, color=INK)
    bx.set_xticks(xs, [f"basin {n}" for n in NAMES])
    bx.set_ylim(0, 0.6)
    bx.set_ylabel("population")
    bx.legend(loc="lower center", bbox_to_anchor=(0.5, 1.0), fontsize=7.5, handlelength=1.0)
    save(fig, "density.png", tight=False)
    for i in range(3):
        NUM[f"pop{NAMES[i]}"] = fmt(L.pop[i], 2)
        NUM[f"occRun{NAMES[i]}"] = fmt(occ[i], 2)


# ----------------------------------------------------------------------------------------
# Part 3 definitions that the deck script does not transcribe.
def innov_cov(a, P, R, K, k):
    """innovCov a P R K k: the innovation autocovariance at lag k + 1."""
    c = a * (1 - K) * P - a * K * R
    for _ in range(k):
        c = a * (1 - K) * c
    return c


def switch_cov(alpha, beta, lam, c1, n):
    """switchCov alpha beta lam c1 n: the lag n + 1 covariance when a hidden switch leaks in."""
    c = c1
    for m in range(n):
        c = alpha * c + beta * lam ** (m + 1)
    return c


class Arrow3D(FancyArrowPatch):
    """A 2D arrow drawn between the projections of two 3D points."""

    def __init__(self, p, q, **kw):
        super().__init__((0, 0), (0, 0), **kw)
        self._pq = np.array([p, q], float)

    def do_3d_projection(self, renderer=None):
        xs, ys, zs = proj3d.proj_transform(*self._pq.T, self.axes.M)
        self.set_positions((xs[0], ys[0]), (xs[1], ys[1]))
        return float(np.min(zs))


def fig_switching():
    """The surrogate in 3D: one quadratic bowl per basin, jumps between the bowls."""
    L = land()
    fit = fit_surrogate(L)
    elev, azim = 54, -72
    view = view_vector(elev, azim)
    light = unit(view + np.array([-0.4, 0.3, 1.0]))
    fig = plt.figure(figsize=(6.4, 3.0))
    ax = fig.add_axes([-0.12, -0.26, 1.24, 1.5], projection="3d")
    clean_3d(ax)
    ax.view_init(elev, azim)
    ax.set_proj_type("persp", focal_length=1.8)
    rim, height = 0.8, 1.0
    curv = height / rim ** 2
    order = np.argsort([m @ view[:2] for m in L.minima])
    label_at = {0: (-1.3, -0.15, 0.5), 1: (1.3, -0.15, 0.5), 2: (0.0, 1.05, 1.25)}
    for k, i in enumerate(order):
        cx, cy = L.minima[i]
        rad, th = np.meshgrid(np.linspace(0, rim, 32), np.linspace(0, 2 * np.pi, 96))
        x, y = cx + rad * np.cos(th), cy + rad * np.sin(th)
        n = np.stack([-2 * curv * (x - cx), -2 * curv * (y - cy), np.ones_like(x)], axis=-1)
        n = n * np.sign((n * view).sum(-1, keepdims=True) + 1e-12)
        cols = phong(n, tint(BASIN[i], 0.7), view, light, amb=0.52, dif=0.5, spec=0.2)
        ax.plot_surface(x, y, curv * rad ** 2, facecolors=cols, rstride=1, cstride=1,
                        linewidth=0, antialiased=False, shade=False, zorder=1 + 2 * k)
        t = np.linspace(0, 2 * np.pi, 120)
        ax.plot(cx + rim * np.cos(t), cy + rim * np.sin(t), np.full(120, height),
                color=BASIN[i], lw=0.9, zorder=2 + 2 * k)
        dx, dy, z = label_at[i]
        ax.text(cx + dx, cy + dy, z, f"basin {NAMES[i]}", ha="center", fontsize=9.5,
                color=INK, zorder=30, **BOLD)
    rng = np.random.default_rng(5)
    cx, cy = L.minima[0]
    q = np.zeros((160, 2))
    for t in range(1, 160):
        q[t] = 0.93 * q[t - 1] + 0.07 * rng.standard_normal(2)
    zq = curv * (q ** 2).sum(1) + 0.03
    ax.plot(cx + q[:, 0], cy + q[:, 1], zq, color=tuple(0.5 * np.array(to_rgb(BLUE))),
            lw=0.6, zorder=8)
    ax.scatter([cx + q[-1, 0]], [cy + q[-1, 1]], [zq[-1] + 0.02], s=26, color=INK,
               edgecolor="white", linewidths=0.8, depthshade=False, zorder=9)
    ax.text(cx, cy - 1.15, 0.0, "inside a bowl: OU motion", fontsize=8.5,
            color=INK2, ha="center", zorder=30)
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        ci, cj = L.minima[i], L.minima[j]
        d = (cj - ci) / np.linalg.norm(cj - ci)
        p = np.r_[ci + 0.5 * rim * d, height + 0.08]
        r_ = np.r_[cj - 0.5 * rim * d, height + 0.08]
        ctrl = (p + r_) / 2 + np.array([0, 0, 0.9])
        s = np.linspace(0, 1, 80)[:, None]
        arc = (1 - s) ** 2 * p + 2 * s * (1 - s) * ctrl + s ** 2 * r_
        ax.plot(*arc[4:-4].T, color=INK2, lw=1.0, zorder=20)
        for a_, b_ in [(arc[6], arc[0]), (arc[-7], arc[-1])]:
            ax.add_artist(Arrow3D(a_, b_, arrowstyle="-|>", mutation_scale=9, color=INK2,
                                  lw=1.0, zorder=21))
        out = arc[40, :2] - L.minima.mean(axis=0)
        mid = arc[40] + np.r_[0.6 * out / np.linalg.norm(out), 0.0]
        ax.text(*mid, rf"$k_{{{NAMES[i]}{NAMES[j]}}},\ k_{{{NAMES[j]}{NAMES[i]}}}$",
                fontsize=9, ha="center", va="center", color=INK, zorder=31)
    ax.set_xlim(-2.2, 2.2)
    ax.set_ylim(-2.0, 2.2)
    ax.set_zlim(-0.2, 2.3)
    ax.set_box_aspect((1, 1, 0.5))
    save(fig, "switching.png", tight=False)
    for i in range(3):
        NUM[f"sigmaSq{NAMES[i]}"] = fmt(fit["s2"][i], 2)
        NUM[f"decay{NAMES[i]}"] = fmt(fit["a"][i], 2)


def fig_ou():
    """An OU mode forgets its start: densities over time, as a waterfall."""
    tau_c, s2, z0, v0 = 10.0, 1.0, 2.4, 0.06
    a = float(np.exp(-1 / tau_c))
    ns = np.arange(0, 46, 3)
    zz = np.linspace(-3.6, 3.6, 300)
    fig = plt.figure(figsize=(6.4, 2.9))
    ax = fig.add_axes([-0.12, -0.25, 1.24, 1.5], projection="3d")
    clean_3d(ax)
    ax.view_init(24, -72)
    ax.set_proj_type("persp", focal_length=4.0)
    span = ns.max()
    for k, n in enumerate(ns):
        mean, var = a ** n * z0, a ** (2 * n) * v0 + s2 * (1 - a ** (2 * n))
        dens = np.exp(-(zz - mean) ** 2 / (2 * var)) / np.sqrt(2 * np.pi * var)
        yv = span - n
        verts = np.c_[np.r_[zz[0], zz, zz[-1]], np.full(len(zz) + 2, yv),
                      np.r_[0, dens, 0]]
        col = tint(BLUE, 0.18 + 0.62 * k / (len(ns) - 1))
        ax.add_collection3d(Poly3DCollection([verts], facecolor=col, edgecolor="none",
                                             alpha=0.92, zorder=2 * k + 1))
        ax.plot(zz, np.full_like(zz, yv), dens, color=tuple(0.7 * np.array(to_rgb(BLUE))),
                lw=0.6, zorder=2 * k + 2)
    nn = np.linspace(0, span, 200)
    mean = a ** nn * z0
    sd = np.sqrt(a ** (2 * nn) * v0 + s2 * (1 - a ** (2 * nn)))
    ax.plot(mean, span - nn, 0 * nn, color=ORANGE, lw=1.3, zorder=0)
    for sgn in (-1, 1):
        ax.plot(mean + 2 * sgn * sd, span - nn, 0 * nn, color=ORANGE, lw=0.7,
                ls=(0, (3, 2)), zorder=0)
    ax.text(z0 - 0.2, span + 1, 1.75, "start: $z_0 = 2.4$,\nknown almost exactly",
            fontsize=8.5, color=INK, zorder=60, ha="right")
    ax.text(3.8, -2.5, 0.12, r"later: $\mathcal{N}(0,\sigma^2)$," + "\nthe basin's spread",
            fontsize=8.5, color=INK, zorder=60, ha="left", va="bottom")
    ax.text(-3.5, span * 0.62, 0.0, r"mean $a^n z_0$, $\pm 2$ s.d.", fontsize=8,
            color=ORANGE, zorder=60, ha="right")
    ax.text(0, -4.5, 0, r"position $z$", fontsize=8.5, color=INK2, ha="center", zorder=60)
    ax.text(3.9, span * 0.75, 0, r"frame $n$ $\rightarrow$", fontsize=8.5, color=INK2,
            zorder=60)
    ax.set_xlim(-3.6, 3.6)
    ax.set_ylim(-3, span + 3)
    ax.set_zlim(0, 1.7)
    ax.set_box_aspect((1.3, 1.4, 0.55))
    save(fig, "ou.png", tight=False)
    NUM.update(ouTau=f"{tau_c:g}", ouA=fmt(a, 3), ouStart=f"{z0:g}")


def joint_density(X, Y, P, R, m=0.0):
    """Density of (state x, reading y = x + v) with x ~ N(m, P), v ~ N(0, R) independent."""
    det = P * R
    dx, dy = X - m, Y - m
    quad = ((P + R) * dx ** 2 - 2 * P * dx * dy + P * dy ** 2) / det
    return np.exp(-quad / 2) / (2 * np.pi * np.sqrt(det))


def fig_bayes():
    """Observing a reading slices the joint density; the slice is the posterior."""
    P, R, m, y0 = 4.0, 1.0, 0.0, 3.0
    K, var = deck.gain(P, R), deck.opt_var(P, R)
    mean = m + K * (y0 - m)
    x = np.linspace(-6, 7, 200)
    y = np.r_[np.linspace(-4.5, y0, 150), np.linspace(y0, 8.0, 100)[1:]]
    X, Y = np.meshgrid(x, y)
    F = joint_density(X, Y, P, R, m)
    cmap = plt.matplotlib.colors.LinearSegmentedColormap.from_list(
        "paper", ["#ffffff", tint(BLUE, 0.3), BLUE])
    ls = LightSource(azdeg=300, altdeg=42)
    rgb = ls.shade(F, cmap=cmap, blend_mode="soft", vert_exag=40, fraction=0.6,
                   vmin=0, vmax=F.max())[..., :3]
    fig = plt.figure(figsize=(6.4, 2.8))
    ax = fig.add_axes([-0.08, -0.17, 0.78, 1.32], projection="3d")
    clean_3d(ax)
    ax.view_init(36, -58)
    ax.set_proj_type("persp", focal_length=2.2)
    back = Y[:, 0] <= y0
    front = Y[:, 0] >= y0
    zmax = F.max() * 1.12
    peak = joint_density(mean, y0, P, R, m)
    kw = dict(rstride=1, cstride=1, linewidth=0, antialiased=False, shade=False)
    ax.plot_surface(X[back], -Y[back], F[back], facecolors=rgb[back], zorder=1, **kw)
    top = 1.7 * peak
    plane = np.array([[x[0], -y0, 0], [x[-1], -y0, 0], [x[-1], -y0, top], [x[0], -y0, top]])
    ax.add_collection3d(Poly3DCollection([plane], facecolor=tint(ORANGE, 0.5), alpha=0.13,
                                         edgecolor=ORANGE, linewidth=0.7, zorder=2))
    ax.plot(x, np.full_like(x, -y0), joint_density(x, y0, P, R, m) + 1e-4, color=ORANGE,
            lw=1.8, zorder=3)
    ax.plot_surface(X[front], -Y[front], F[front], facecolors=rgb[front], zorder=4, **kw)
    ax.text(mean + 1.6, -y0, peak * 1.05, "slice = posterior\n(up to a constant)",
            fontsize=8, color=ORANGE, zorder=10)
    fig.text(0.02, 0.93, "surface: joint density of state $x$ and reading $y$", fontsize=8,
             color=INK2, va="top")
    fig.text(0.02, 0.86, rf"plane: the reading $y = {y0:g}$ is observed", fontsize=8,
             color=ORANGE, va="top")
    ax.set_xlim(x[0], x[-1])
    ax.set_ylim(-y[-1], -y[0])
    ax.set_zlim(0, zmax)
    ax.set_box_aspect((1.15, 1.0, 0.5))
    bx = fig.add_axes([0.715, 0.2, 0.28, 0.6])
    xx = np.linspace(-6, 7, 600)

    def pdf(mu, v):
        return np.exp(-(xx - mu) ** 2 / (2 * v)) / np.sqrt(2 * np.pi * v)

    for mu, v, c, lab in [(m, P, BLUE, rf"prior: mean {m:g}, var $P = {P:g}$"),
                          (y0, R, ORANGE, rf"reading: {y0:g}, var $R = {R:g}$"),
                          (mean, var, AQUA, rf"posterior: {mean:g}, var {var:g}")]:
        bx.plot(xx, pdf(mu, v), color=c, label=lab)
        bx.fill_between(xx, pdf(mu, v), color=c, alpha=0.1, lw=0)
    bx.set_xlabel("state $x$")
    bx.set_ylabel("density")
    bx.set_ylim(0, 0.56)
    bx.legend(loc="lower center", bbox_to_anchor=(0.45, 1.0), fontsize=7.5, handlelength=1.2)
    save(fig, "bayes.png", tight=False)
    NUM.update(bP=f"{P:g}", bR=f"{R:g}", bY=f"{y0:g}", bK=f"{K:g}", bMean=f"{mean:g}",
               bVar=f"{var:g}")


def fig_valley():
    """postVar P R K as a surface over (K, P): the Kalman gain runs along the valley floor."""
    R = 1.0
    K = np.linspace(-0.15, 1.15, 131)
    P = np.linspace(0.2, 4.0, 131)
    KK, PP = np.meshgrid(K, P)
    F = deck.post_var(PP, R, KK)
    cmap = plt.matplotlib.colors.LinearSegmentedColormap.from_list(
        "valley", [tint(AQUA, 0.25), "#ffffff", tint(BLUE, 0.45), BLUE])
    ls = LightSource(azdeg=225, altdeg=40)
    rgb = ls.shade(F, cmap=cmap, blend_mode="soft", vert_exag=0.5, fraction=0.7,
                   vmin=0, vmax=F.max())[..., :3]
    fig = plt.figure(figsize=(4.4, 3.3))
    ax = fig.add_axes([0, 0, 1, 1], projection="3d")
    ax.computed_zorder = False
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor((1, 1, 1, 0))
        axis.pane.set_edgecolor(GRID)
        axis._axinfo["grid"].update(color=GRID, linewidth=0.4)
        axis.label.set_color(INK2)
    ax.view_init(30, -128)
    ax.set_proj_type("persp", focal_length=2.2)
    ax.plot_surface(KK, PP, F, facecolors=rgb, rstride=1, cstride=1, linewidth=0,
                    antialiased=False, shade=False, zorder=1)
    Pl = np.linspace(P[0], P[-1], 200)
    ax.plot(deck.gain(Pl, R), Pl, deck.opt_var(Pl, R) + 0.02, color=ORANGE, lw=2.0, zorder=5)
    ax.plot(K, np.full_like(K, P[-1]), deck.post_var(P[-1], R, K), color=INK, lw=1.0,
            ls=(0, (3, 2)), zorder=6)
    ax.text2D(0.5, 0.86, r"orange: the valley floor," + "\n" + r"$K^* = P/(P+R)$, height "
              r"$\mathrm{optVar}\ P\ R$", transform=ax.transAxes, fontsize=8, color=INK,
              ha="left", va="top")
    ax.text2D(0.02, 0.86, r"dashed: the slice $P = 4$", transform=ax.transAxes, fontsize=8,
              color=INK2, va="top")
    ax.set_xlabel("gain $K$", labelpad=-2)
    ax.set_ylabel("prior variance $P$", labelpad=-1)
    ax.set_zlabel("", labelpad=-4)
    ax.tick_params(labelsize=7, pad=-2)
    ax.set_box_aspect((1, 1, 0.75), zoom=0.92)
    ax.text2D(0.02, 0.93, r"$\mathrm{postVar}\ P\ R\ K$ with $R = 1$", transform=ax.transAxes,
              fontsize=9, color=INK2)
    save(fig, "valley.png")


# ----------------------------------------------------------------------------------------
# Diagrams.
def diagram(w_in, h_in, W=10.0, y0=0.0):
    """A blank canvas W units wide with equal x and y units, starting at height y0."""
    fig = plt.figure(figsize=(w_in, h_in))
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, W)
    ax.set_ylim(y0, y0 + W * h_in / w_in)
    ax.axis("off")
    return fig, ax


def box(ax, x, y, w, h, color, fill=0.12, lw=0.9, rounding=0.1):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle=f"round,pad=0,rounding_size={rounding}",
                                facecolor=tint(color, fill), edgecolor=color, lw=lw))


def arrow(ax, p, q, color=INK2, rad=0.0, lw=0.9, style="-|>", ms=9, shrink=1.5):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle=style, mutation_scale=ms, color=color, lw=lw,
                                 connectionstyle=f"arc3,rad={rad}", shrinkA=shrink,
                                 shrinkB=shrink))


def fig_frame():
    """One frame of the model and the filter: hidden state, sensors, predict, correct."""
    fig, ax = diagram(6.4, 2.75)
    H = 10 * 2.75 / 6.4
    box(ax, 0.1, 1.55, 1.95, 1.1, INK2, fill=0.06)
    ax.text(1.075, 2.32, "slow state", ha="center", fontsize=9, **BOLD)
    ax.text(1.075, 1.88, "$z_n$ (hidden)", ha="center", fontsize=9)
    ax.text(1.075, 1.2, "OU step each frame:\n$z_{n+1} = a\\,z_n + w_n$\n"
            r"$\mathrm{Var}\,w_n = Q$", ha="center", va="top", fontsize=8, color=INK2)
    ax.text(3.7, H - 0.28, "sensors (coordinate families)", ha="center", fontsize=8.5,
            color=INK2)
    sensors = [2.85, 1.75, 0.65]
    for k, yb in enumerate(sensors):
        box(ax, 2.75, yb, 1.9, 0.8, ORANGE, fill=0.1)
        ax.text(3.7, yb + 0.52, rf"$y_{k + 1} = z_n + v_{k + 1}$", ha="center", fontsize=9)
        ax.text(3.7, yb + 0.2, rf"noise variance $R_{k + 1}$", ha="center", fontsize=7.5,
                color=INK2)
        arrow(ax, (2.05, 2.1), (2.75, yb + 0.4))
    box(ax, 5.3, 0.3, 2.75, 3.55, BLUE, fill=0.05)
    ax.text(6.675, 3.56, "Kalman filter", ha="center", fontsize=9, **BOLD)
    box(ax, 5.5, 2.3, 2.35, 1.0, BLUE, fill=0.14)
    ax.text(6.675, 3.05, "predict", ha="center", fontsize=8.5, color=INK2)
    ax.text(6.675, 2.55, r"$m^- = a\,m,\quad P^- = a^2 P + Q$", ha="center", fontsize=8.5)
    box(ax, 5.5, 0.5, 2.35, 1.45, BLUE, fill=0.14)
    ax.text(6.675, 1.72, "correct (one sensor)", ha="center", fontsize=8.5, color=INK2)
    ax.text(6.675, 1.33, r"$K = P^-/(P^- + R)$", ha="center", fontsize=8.5)
    ax.text(6.675, 1.0, r"$m = m^- + K\,(y - m^-)$", ha="center", fontsize=8.5)
    ax.text(6.675, 0.66, r"$P = P^- R/(P^- + R)$", ha="center", fontsize=8.5)
    for k, yb in enumerate(sensors):
        arrow(ax, (4.65, yb + 0.4), (5.5, 1.55 - 0.3 * k))
    arrow(ax, (6.3, 2.3), (6.3, 1.95))
    arrow(ax, (7.05, 1.95), (7.05, 2.3), rad=0.0)
    ax.text(7.12, 2.12, "next frame", fontsize=7, color=INK2, va="center")
    box(ax, 8.55, 2.35, 1.4, 1.0, AQUA, fill=0.14)
    ax.text(9.25, 3.05, "estimate", ha="center", fontsize=8.5, color=INK2)
    ax.text(9.25, 2.6, r"$m_n \pm \sqrt{P_n}$", ha="center", fontsize=8.5)
    box(ax, 8.55, 0.5, 1.4, 1.35, AQUA, fill=0.14)
    ax.text(9.25, 1.6, "innovation", ha="center", fontsize=8.5, color=INK2)
    ax.text(9.25, 1.2, r"$\nu_n = y_n - m_n^-$", ha="center", fontsize=8.5)
    ax.text(9.25, 0.75, "tests: size\nand pattern", ha="center", va="center", fontsize=7.5,
            color=INK2)
    arrow(ax, (7.85, 2.8), (8.55, 2.85))
    arrow(ax, (7.85, 1.0), (8.55, 1.1))
    save(fig, "frame.pdf")


def fig_two_state():
    """The two-state switch (H0) and its fingerprint in the innovations (H)."""
    fig = plt.figure(figsize=(6.4, 2.35))
    ax = fig.add_axes([0.0, 0.0, 0.46, 1.0])
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10 * 2.35 / (0.46 * 6.4))
    ax.axis("off")
    p = q = 0.02
    r, cA, cB = 1.05, np.array([3.0, 3.6]), np.array([7.0, 3.6])
    for c, col, name in [(cA, BLUE, "A"), (cB, ORANGE, "B")]:
        ax.add_patch(Circle(c, r, facecolor=tint(col, 0.16), edgecolor=col, lw=1.4))
        ax.text(*c, name, ha="center", va="center", fontsize=15, **BOLD)
    arrow(ax, cA + [0.7, 0.8], cB + [-0.7, 0.8], rad=-0.35, ms=10)
    arrow(ax, cB + [-0.7, -0.8], cA + [0.7, -0.8], rad=-0.35, ms=10)
    ax.text(5.0, 5.55, "$p$", ha="center", fontsize=11)
    ax.text(5.0, 1.35, "$q$", ha="center", fontsize=11)
    for c, sgn, lab in [(cA, -1, "$1-p$"), (cB, 1, "$1-q$")]:
        s = c + [sgn * r * 0.8, r * 0.6]
        e = c + [sgn * r * 0.8, -r * 0.6]
        arrow(ax, s, e, rad=-1.6 * sgn, ms=9)
        ax.text(c[0] + sgn * 2.55, c[1], lab, ha="center", va="center", fontsize=10)
    ax.text(5.0, 0.35, r"eigenvalues $1$ and $\lambda = 1-p-q$", ha="center", fontsize=9,
            color=INK2)
    bx = fig.add_axes([0.56, 0.2, 0.43, 0.7])
    a, R = 0.5, 0.2
    P = deck.ou_riccati(a, 1.0, R, 1000)[-1]
    K = deck.gain(P, R)
    alpha, lam, beta, c1 = a * (1 - K), 1 - p - q, 0.02, 0.12
    n = np.arange(0, 61)
    c = np.array([switch_cov(alpha, beta, lam, c1, k) for k in n])
    B = beta * lam / (lam - alpha)
    bx.semilogy(n + 1, c, color=INK, lw=1.4, label=r"$c_{n}$ (switchCov)")
    bx.semilogy(n + 1, (c1 - B) * alpha ** n, color=BLUE, lw=1.0, ls=(0, (3, 2)),
                label=r"filter part $\propto \alpha^n$")
    bx.semilogy(n + 1, B * lam ** n, color=ORANGE, lw=1.0, ls=(0, (3, 2)),
                label=r"switch part $\propto \lambda^n$")
    bx.set_ylim(1e-4, 0.3)
    bx.set_xlabel("lag")
    bx.set_ylabel("innovation covariance")
    bx.legend(loc="upper right", fontsize=7.5)
    ratio = c[-1] / c[-2]
    bx.set_title(rf"$c_{{n+1}}/c_n \to \lambda$: {ratio:.4f} at lag 61", loc="left",
                 fontsize=8.5, color=INK2)
    save(fig, "two_state.pdf")
    NUM.update(hAlpha=fmt(alpha, 3), hLam=f"{lam:g}", hRatio=f"{ratio:.4f}", hP=f"{p:g}")


def three_basin_check():
    """The deck's figure 14 experiment (same seed and call order), returned as numbers."""
    rng = np.random.default_rng(14)
    p = np.array([0.5, 0.3, 0.2])
    kappa = rng.uniform(0.5, 2.0, (3, 3))
    kappa = (kappa + kappa.T) / 2
    L = deck.generator(kappa, p)
    outflow = -np.diag(L)
    jumps = 200_000
    u, w = rng.random(jumps), rng.exponential(1.0, jumps)
    others = [[j for j in range(3) if j != i] for i in range(3)]
    first = [L[i, others[i][0]] / outflow[i] for i in range(3)]
    occ, state = np.zeros(3), 0
    for k in range(jumps):
        occ[state] += w[k] / outflow[state]
        state = others[state][0] if u[k] < first[state] else others[state][1]
    return p, kappa, L, occ / occ.sum(), jumps


def fig_three_basins():
    """M in numbers: rates k_ij = kappa_ij sqrt(p_j / p_i) and the balanced flows."""
    p, kappa, L, occ, jumps = three_basin_check()
    fig, ax = diagram(6.4, 2.75)
    pos = {0: np.array([2.2, 1.05]), 1: np.array([7.8, 1.05]), 2: np.array([5.0, 3.3])}
    for i, c in pos.items():
        rr = 0.95 * np.sqrt(p[i] / p.max())
        ax.add_patch(Circle(c, rr, facecolor=tint(BASIN[i], 0.2), edgecolor=BASIN[i], lw=1.4))
        ax.text(c[0], c[1] + 0.12, NAMES[i], ha="center", va="center", fontsize=13, **BOLD)
        ax.text(c[0], c[1] - 0.3, f"$p_{NAMES[i]} = {p[i]:g}$", ha="center", va="center",
                fontsize=8.5)
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        a_, b_ = pos[i], pos[j]
        d = (b_ - a_) / np.linalg.norm(b_ - a_)
        nrm = np.array([-d[1], d[0]])
        ri = 0.95 * np.sqrt(p[i] / p.max()) + 0.12
        rj = 0.95 * np.sqrt(p[j] / p.max()) + 0.12
        for sgn, (s, t) in [(1, (i, j)), (-1, (j, i))]:
            off = 0.2 * sgn * nrm
            start = pos[s] + (ri if s == i else rj) * (pos[t] - pos[s]) / np.linalg.norm(
                pos[t] - pos[s]) + off
            end = pos[t] - (rj if t == j else ri) * (pos[t] - pos[s]) / np.linalg.norm(
                pos[t] - pos[s]) + off
            arrow(ax, start, end, ms=8, lw=0.9)
            mid = (start + end) / 2 + 0.36 * sgn * nrm
            angle = np.degrees(np.arctan2(d[1], d[0]))
            angle = angle - 180 if angle > 90 else angle + 180 if angle <= -90 else angle
            ax.text(*mid, rf"$k_{{{NAMES[s]}{NAMES[t]}}} = {L[s, t]:.2f}$", fontsize=8,
                    ha="center", va="center", color=INK, rotation=angle,
                    rotation_mode="anchor")
        flow = p[i] * L[i, j]
        assert abs(flow - p[j] * L[j, i]) < 1e-12
        NUM[f"mFlow{NAMES[i]}{NAMES[j]}"] = f"{flow:.3f}"
        NUM[f"mKappa{NAMES[i]}{NAMES[j]}"] = f"{kappa[i, j]:.3f}"
        NUM[f"mRate{NAMES[i]}{NAMES[j]}"] = f"{L[i, j]:.3f}"
        NUM[f"mRate{NAMES[j]}{NAMES[i]}"] = f"{L[j, i]:.3f}"
    save(fig, "three_basins.pdf")
    res = float(np.max(np.abs(p @ L)))
    exp10 = int(np.floor(np.log10(res))) if res > 0 else 0
    NUM.update(mRes=("0" if res == 0 else rf"{res / 10 ** exp10:.0f}\times 10^{{{exp10}}}"),
               mJumps=f"{jumps:,}", mOccErr=f"{np.max(np.abs(occ - p)):.3f}",
               mOcc=", ".join(f"{v:.3f}" for v in occ))


# ----------------------------------------------------------------------------------------
# The filter over time and its diagnostics (one OU mode, as in the deck's figure 11).
def ou_mode():
    """Relaxation time 10 frames, equilibrium variance 1, sensor noise 0.5."""
    tau_c, s2, R = 10.0, 1.0, 0.5
    a = float(np.exp(-1 / tau_c))
    return a, s2 * (1 - a * a), R, s2, tau_c


def fig_filter_run():
    """A simulated OU mode, its noisy readings, and the Kalman estimate with its band."""
    a, Q, R, s2, _ = ou_mode()
    rng = np.random.default_rng(11)
    n, P0 = 100, 5.0
    z = np.empty(n)
    z[0] = rng.normal(0, np.sqrt(s2))
    for t in range(1, n):
        z[t] = a * z[t - 1] + rng.normal(0, np.sqrt(Q))
    y = z + rng.normal(0, np.sqrt(R), n)
    m_prior, P_prior = 0.0, P0
    est, post, prior = np.empty(n), np.empty(n), np.empty(n)
    for t in range(n):
        prior[t] = P_prior
        est[t] = m_prior + deck.gain(P_prior, R) * (y[t] - m_prior)
        post[t] = deck.opt_var(P_prior, R)
        m_prior, P_prior = a * est[t], deck.riccati_step(a, Q, R, P_prior)
    Pinf = float(deck.steady_var(a, Q, R))
    t = np.arange(n)
    fig, (a1, a2) = plt.subplots(2, 1, figsize=(6.4, 3.6), sharex=True,
                                 gridspec_kw=dict(height_ratios=[1.7, 1]))
    sd = np.sqrt(post)
    a1.fill_between(t, est - 2 * sd, est + 2 * sd, color=tint(BLUE, 0.16), lw=0,
                    label=r"$m_n \pm 2$ s.d.")
    a1.plot(t, y, "o", ms=2.2, color=MUTED, label="readings $y_n$")
    a1.plot(t, z, color=INK, lw=1.1, label="hidden state $z_n$")
    a1.plot(t, est, color=BLUE, lw=1.3, label="estimate $m_n$")
    a1.set_ylabel("value")
    a1.legend(loc="upper center", ncol=4, bbox_to_anchor=(0.5, 1.2), fontsize=7.5)
    a2.semilogy(t, prior, color=BLUE, label=r"before the reading, $P_n$")
    a2.semilogy(t, post, color=AQUA, label="after the reading")
    a2.axhline(Pinf, color=INK2, lw=0.8, ls=(0, (3, 2)))
    a2.axhline(deck.opt_var(Pinf, R), color=INK2, lw=0.8, ls=(0, (3, 2)))
    a2.text(n - 1, Pinf * 1.12, rf"$P_\infty = {Pinf:.3f}$", ha="right", fontsize=8)
    a2.text(n - 1, deck.opt_var(Pinf, R) * 1.12,
            rf"$\mathrm{{optVar}}(P_\infty, R) = {deck.opt_var(Pinf, R):.3f}$", ha="right",
            fontsize=8)
    a2.set_yticks([0.2, 0.5, 1, 2, 5], ["0.2", "0.5", "1", "2", "5"])
    a2.minorticks_off()
    a2.set_ylabel("variance")
    a2.set_xlabel("frame $n$")
    a2.set_xlim(0, n - 1)
    a2.legend(loc="upper right", fontsize=7.5)
    fig.tight_layout(h_pad=0.4)
    save(fig, "filter_run.pdf")
    late = t >= 20
    inside = np.abs(z - est) <= 2 * sd
    NUM.update(Pinf=fmt(Pinf), PpostInf=fmt(deck.opt_var(Pinf, R)), Sinf=fmt(Pinf + R),
               gainInf=fmt(deck.gain(Pinf, R)), runA=fmt(a), runQ=fmt(Q), runR=f"{R:g}",
               runPzero=f"{P0:g}", runIn=str(int(inside[late].sum())),
               runLate=str(int(late.sum())))


def fig_riccati():
    """The variance recursion as a cobweb, and every gap under its (a^2)^n bound."""
    a, Q, R, _, _ = ou_mode()
    Pinf = float(deck.steady_var(a, Q, R))
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.4, 2.75))
    top = 1.0
    grid = np.linspace(0, top, 300)
    a1.plot(grid, grid, color=AXIS, lw=0.8)
    a1.plot(grid, deck.riccati_step(a, Q, R, grid), color=INK, lw=1.3,
            label=r"$P \mapsto a^2\,\mathrm{optVar}(P,R) + Q$")
    for P0, col in [(top, BLUE), (0.0, ORANGE)]:
        P, xs, ys = P0, [P0], [0.0]
        for _ in range(7):
            nxt = deck.riccati_step(a, Q, R, P)
            xs += [P, nxt]
            ys += [nxt, nxt]
            P = nxt
        a1.plot(xs, ys, color=col, lw=0.9, label=f"start $P_0 = {P0:g}$")
    a1.plot([Pinf], [Pinf], "o", ms=5, color=INK, mec="white", mew=1, zorder=5)
    a1.annotate(rf"fixed point $P_\infty = {Pinf:.3f}$", xy=(Pinf, Pinf), xytext=(0.45, 0.2),
                fontsize=8, arrowprops=dict(arrowstyle="-", color=INK2, lw=0.7))
    a1.set_xlim(0, top)
    a1.set_ylim(0, top)
    a1.set_aspect("equal")
    a1.set_xlabel("$P_n$")
    a1.set_ylabel("$P_{n+1}$")
    a1.legend(loc="upper left", fontsize=7.2)
    a1.set_title("(a) one step at a time", loc="left", fontsize=9, color=INK2)
    worst, steps = 0.0, np.arange(41)
    for P0, col in zip([0.0, 0.1, 1.0, 2.5, 5.0], RAMP):
        P = deck.riccati_iter(a, Q, R, P0, 40)
        gap, bound = np.abs(P - Pinf), (a * a) ** steps * abs(P0 - Pinf)
        worst = max(worst, float(np.max(gap[1:] / bound[1:])))
        keep = gap > 1e-15
        a2.semilogy(steps[keep], gap[keep], color=col, lw=1.1)
        a2.semilogy(steps, bound, color=col, lw=0.8, ls=(0, (3, 2)))
    a2.plot([], [], color=INK2, label=r"gap $|P_n - P_\infty|$")
    a2.plot([], [], color=INK2, lw=0.8, ls=(0, (3, 2)), label=r"bound $(a^2)^n|P_0 - P_\infty|$")
    a2.set_ylim(1e-16, 30)
    a2.set_xlabel("frame $n$")
    a2.legend(loc="lower left", fontsize=7.2)
    a2.set_title("(b) five starts, every gap under its bound", loc="left", fontsize=9,
                 color=INK2)
    fig.tight_layout(w_pad=1.5)
    save(fig, "riccati.pdf")
    NUM.update(rWorst=f"{worst:.2f}", rAsq=fmt(a * a), rSlope=fmt(
        a * a * R ** 2 / (Pinf + R) ** 2))


def innovation_experiment():
    """The deck's figure 6 experiment (seed 6): channel 4 omits a hidden coordinate h."""
    rng = np.random.default_rng(6)
    P = 0.6
    Rc = np.array([0.4, 0.8, 0.5, 1.0, 0.3, 0.6])
    flagged, N = 3, 200_000
    S = P + Rc
    tau2 = 3 * S[flagged]
    e = rng.normal(0, np.sqrt(P), N)
    nus = []
    for c in range(len(Rc)):
        nu = e + rng.normal(0, np.sqrt(Rc[c]), N)
        if c == flagged:
            nu = nu + rng.normal(0, np.sqrt(tau2), N)
        nus.append(nu)
    return nus, S, flagged, N


def autocorr_experiment():
    """The deck's figure 7 experiment (seed 7): a filter that ignores a hidden switch."""
    rng = np.random.default_rng(7)
    a, R, p, q, s2, amp = 0.5, 0.2, 0.02, 0.02, 1.0, 1.0
    N, burn, maxlag = 1_000_000, 1_000, 60
    P = s2
    for _ in range(1000):
        P = deck.ou_predict(a, s2, deck.opt_var(P, R))
    K = deck.gain(P, R)
    alpha, lam2 = a * (1 - K), 1 - p - q
    s = deck.two_state_chain(rng, p, q, N + burn)
    w = rng.normal(0, np.sqrt(s2 * (1 - a * a)), N + burn)
    x = np.empty(N + burn)
    xt = rng.normal(0, np.sqrt(s2))
    for t, wt in enumerate(w.tolist()):
        x[t] = xt
        xt = a * xt + wt
    y = x + amp * s + rng.normal(0, np.sqrt(R), N + burn)
    naive = deck.acf(deck.innovations(y, alpha, a * K)[burn:], maxlag)
    right = deck.acf(deck.innovations(y - amp * s, alpha, a * K)[burn:], maxlag)
    fit = np.arange(10, 51)
    lam_hat = float(np.exp(np.polyfit(fit, np.log(naive[fit]), 1)[0]))
    return naive, right, lam2, lam_hat, N


def fig_diagnostics():
    """The two innovation tests: size (variance ratio) and pattern (autocorrelation)."""
    nus, S, flagged, N = innovation_experiment()
    naive, right, lam2, lam_hat, Nac = autocorr_experiment()
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.4, 2.6))
    bins = np.linspace(-8, 8, 81)
    ratios = {}
    for c, col, lab in [(0, BLUE, "channel 1 (model right)"),
                        (flagged, ORANGE, f"channel {flagged + 1} (omits $h$)")]:
        std = nus[c] / np.sqrt(S[c])
        ratios[c] = float(nus[c].var() / S[c])
        a1.hist(std, bins=bins, density=True, histtype="stepfilled", color=tint(col, 0.25),
                edgecolor=col, lw=0.8, label=rf"{lab}: ratio {ratios[c]:.2f}")
    xx = np.linspace(-8, 8, 400)
    a1.plot(xx, np.exp(-xx ** 2 / 2) / np.sqrt(2 * np.pi), color=INK, lw=0.9, ls=(0, (3, 2)),
            label=r"predicted $\mathcal{N}(0, 1)$")
    a1.set_xlabel(r"innovation $/\sqrt{S}$")
    a1.set_ylabel("density")
    a1.set_ylim(0, 0.5)
    a1.legend(loc="upper left", fontsize=6.8)
    a1.set_title("(a) size: variance / predicted $S$", loc="left", fontsize=9, color=INK2)
    lags = np.arange(1, len(naive))
    a2.axhline(0, color=AXIS, lw=0.7)
    a2.plot(lags, naive[1:], color=ORANGE, label="filter ignores the switch")
    a2.plot(lags, right[1:], color=BLUE, label="filter knows the switch")
    ref = naive[10] * lam2 ** (lags - 10)
    a2.plot(lags, ref, color=INK, lw=0.8, ls=(0, (3, 2)), label=rf"$\propto \lambda^k$, "
            rf"$\lambda = {lam2:g}$")
    a2.set_xlabel("lag $k$")
    a2.set_ylabel("autocorrelation")
    a2.legend(loc="upper right", fontsize=7)
    a2.set_title("(b) pattern: correlation across frames", loc="left", fontsize=9, color=INK2)
    fig.tight_layout(w_pad=1.5)
    save(fig, "diagnostics.pdf")
    NUM.update(dRatioOk=f"{ratios[0]:.2f}", dRatioBad=f"{ratios[flagged]:.2f}",
               dN=f"{N:,}", dLamHat=f"{lam_hat:.3f}", dLam=f"{lam2:g}", dNac=f"{Nac:,}",
               dRhoMax=f"{np.max(np.abs(right[1:])):.4f}", dFlag=str(flagged + 1))


def fig_practice():
    """What F and F5 mean for a run: burn-in length and the detection margin."""
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.4, 2.5))
    ratio = np.logspace(0, 3, 300)
    for eps, col, k, word in [(1e-2, BLUE, 2, "Two"), (1e-3, ORANGE, 3, "Three")]:
        a1.loglog(ratio, deck.burn_in(ratio, eps), color=col, label=rf"$\varepsilon = 10^{{-{k}}}$")
        a1.plot([10], [deck.burn_in(10, eps)], "o", ms=4.5, color=col, mec="white", mew=1)
        NUM[f"burn{word}"] = str(int(np.ceil(deck.burn_in(10.0, eps))))
    a1.set_xlabel(r"relaxation time $\tau_c/\Delta t$")
    a1.set_ylabel("frames to discard")
    a1.legend(loc="upper left", fontsize=7.5)
    a1.set_title(r"(a) burn-in $n \geq \frac{\tau_c}{2\Delta t}\ln\frac{1}{\varepsilon}$",
                 loc="left", fontsize=9, color=INK2)
    x = np.logspace(-3, np.log10(6), 300)
    a2.semilogx(x, 1 + x, color=BLUE, label=r"$1 + \tau^2/S_\infty$ (F5)")
    a2.plot([3.0], [4.0], "o", ms=4.5, color=BLUE, mec="white", mew=1)
    a2.annotate("observed 4x", xy=(3.0, 4.0), xytext=(0.12, 4.2), fontsize=8,
                arrowprops=dict(arrowstyle="-", color=INK2, lw=0.7))
    for N, ls, word in [(1_000, (0, (3, 2)), "K"), (100_000, (0, (1, 1.5)), "H")]:
        thr = 3 * np.sqrt(2 / N)
        a2.axvline(thr, color=INK2, lw=0.8, ls=ls)
        a2.text(thr * 0.85, 5.45, "noise floor, " + f"$N = {N:,}$".replace(",", "{,}"),
                fontsize=7, color=INK2, va="top", ha="right", rotation=90)
        NUM[f"thr{word}"] = f"{thr:.2g}"
    a2.set_xlabel(r"omitted variance $\tau^2/S_\infty$")
    a2.set_ylabel(r"innovation variance $/S_\infty$")
    a2.set_ylim(0.6, 5.6)
    a2.set_title("(b) detection margin", loc="left", fontsize=9, color=INK2)
    fig.tight_layout(w_pad=1.5)
    save(fig, "practice.pdf")


def fig_ladder():
    """From the real system to the Lean theorems, and what guarantees each step."""
    fig, ax = diagram(6.4, 1.5, y0=0.6)
    steps = ["molecular\ndynamics", "switching\ndiffusion", "scalar\npieces",
             "Lean definitions\nand statements", "Lean\nproofs"]
    notes = [("modeling\nassumptions", ORANGE), ("simplify:\nscalar, linear", ORANGE),
             ("translation,\nread by a human", BLUE), ("checked by\nLean's kernel", AQUA)]
    xs = [0.1, 2.15, 4.2, 6.25, 8.45]
    ws = [1.6, 1.6, 1.6, 1.75, 1.45]
    for x, w_, s in zip(xs, ws, steps):
        box(ax, x, 1.25, w_, 1.25, INK2, fill=0.05)
        ax.text(x + w_ / 2, 1.875, s, ha="center", va="center", fontsize=8.5)
    for k, (txt, col) in enumerate(notes):
        x0, x1 = xs[k] + ws[k], xs[k + 1]
        arrow(ax, (x0, 1.875), (x1, 1.875), color=col, lw=1.4, ms=10)
        ax.text((x0 + x1) / 2, 1.05, txt, ha="center", va="top", fontsize=7.3, color=INK)
        ax.add_patch(Circle(((x0 + x1) / 2, 2.15), 0.07, color=col))
    for k, (lab, col) in enumerate([("guaranteed by data (Part II)", ORANGE),
                                    ("by a human reader (Part III)", BLUE),
                                    ("by Lean (Appendix A)", AQUA)]):
        x = 1.0 + 3.0 * k
        ax.add_patch(Circle((x, 2.8), 0.07, color=col))
        ax.text(x + 0.15, 2.8, lab, va="center", fontsize=7.5, color=INK2)
    save(fig, "ladder.pdf")


def fig_lean_file():
    """The parts of Kalman.lean, what each holds, and who checks it."""
    order, info, defs, _ = deck.parse_lean()
    n_def = {p: [n for n, q in defs if q == p] for p in ("1", "3")}
    n_thm = {p: [n for n in order if info[n]["part"] == p]
             for p in ("2", "4", "4b", "4c", "5", "6")}
    rows = [("1", "core definitions", f"{len(n_def['1'])} defs: postVar, gain, optVar", BLUE),
            ("2", "core theorems (the student's)", f"{len(n_thm['2'])} proofs", AQUA),
            ("3", "model definitions", f"{len(n_def['3'])} defs: updErr ... generator", BLUE),
            ("4", "proofs for S, O, W, H0, H", f"{len(n_thm['4'])} proofs", AQUA),
            ("4b", "proofs for F (filter)", f"{len(n_thm['4b'])} proofs", AQUA),
            ("4c", "proofs for M (switching)", f"{len(n_thm['4c'])} proofs", AQUA),
            ("5", "proofs for A, D, F5 (random variables)", f"{len(n_thm['5'])} proofs", AQUA),
            ("6", r"the final statements, $\mathtt{spec\_}\ast$", f"{len(n_thm['6'])} "
             "statements, each proved in one line", BLUE)]
    fig, ax = diagram(6.4, 2.95)
    top, hgt, gap = 4.25, 0.44, 0.08
    for k, (part, what, count, col) in enumerate(rows):
        y = top - k * (hgt + gap)
        box(ax, 0.9, y, 6.6, hgt, col, fill=0.14 if col == BLUE else 0.1, lw=0.8,
            rounding=0.06)
        ax.text(0.75, y + hgt / 2, f"Part {part}", ha="right", va="center", fontsize=8.5,
                **BOLD)
        ax.text(1.05, y + hgt / 2, what, va="center", fontsize=8.5)
        ax.text(7.35, y + hgt / 2, count, va="center", ha="right", fontsize=7.8, color=INK2)
    y6 = top - 7 * (hgt + gap) + hgt / 2
    for part_idx in (1, 3, 4, 5, 6):
        yk = top - part_idx * (hgt + gap) + hgt / 2
        arrow(ax, (7.55, y6), (7.55, yk), rad=0.12 + 0.05 * (6 - part_idx), lw=0.6, ms=6,
              color=MUTED)
    ax.text(8.45, 2.35, "each Part 6\ntheorem cites\none lemma from\na proof Part",
            fontsize=7.5, color=INK2, va="center")
    for k, (lab, col) in enumerate([("read and approved by a human", BLUE),
                                    ("checked by Lean's kernel", AQUA)]):
        x = 1.0 + 3.6 * k
        ax.add_patch(FancyBboxPatch((x, 0.12), 0.32, 0.2, boxstyle="round,pad=0,"
                                    "rounding_size=0.04", facecolor=tint(col, 0.14),
                                    edgecolor=col, lw=0.8))
        ax.text(x + 0.45, 0.22, lab, va="center", fontsize=7.8, color=INK2)
    save(fig, "lean_file.pdf")
    NUM.update(nProofs=str(sum(len(n_thm[p]) for p in ("2", "4", "4b", "4c", "5"))))


# ----------------------------------------------------------------------------------------
FIGURES = [fig_molecule, fig_landscape, fig_timescales, fig_density, fig_switching, fig_ou,
           fig_frame, fig_bayes, fig_valley, fig_filter_run, fig_riccati, fig_diagnostics,
           fig_two_state, fig_three_basins, fig_practice, fig_ladder, fig_lean_file]


def write_numbers():
    lines = ["% Generated by make_writeup_figures.py: every number the text quotes.",
             r"% kalman_writeup.tex reads them as \val{key}."]
    for k in sorted(NUM):
        assert re.fullmatch(r"[A-Za-z0-9]+", k), k
        lines.append(rf"\expandafter\def\csname kfval@{k}\endcsname{{{NUM[k]}}}")
    (GEN / "numbers.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("wrote", GEN / "numbers.tex", f"({len(NUM)} numbers)")


def main(names):
    FIG.mkdir(exist_ok=True)
    GEN.mkdir(exist_ok=True)
    setup_style()
    write_lean_excerpts()
    known = {f.__name__.removeprefix("fig_") for f in FIGURES}
    assert set(names) <= known, f"unknown figures {set(names) - known}; choose from {known}"
    for make in FIGURES:
        if not names or make.__name__.removeprefix("fig_") in names:
            make()
    if not names:
        write_numbers()


if __name__ == "__main__":
    main(sys.argv[1:])

