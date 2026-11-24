#!/usr/bin/env python3
"""The two pictures of the Lean proofs in the explorer: every module of the repository, and the shared
library's definitions and theorems.

    python3 scripts/graphs.py modules REPO OUT [WIDTH]          every Lean module and its imports, by solid
    python3 scripts/graphs.py declarations REPO OUT.tsv         builds the library, dumps its declarations
    python3 scripts/graphs.py library DECLS.tsv OUT [WIDTH]     the library's declarations and their uses

REPO is a checkout of the repository; OUT a .png or .webp (quality 90); WIDTH in pixels (default 3000).
`modules` and `library` need numpy, python-igraph and pillow, e.g.
`uv run --with numpy --with igraph --with pillow python3 scripts/graphs.py modules . modules.webp`.
`declarations` needs Lean (elan, lake): it fetches Mathlib's compiled cache, builds every module of
Definitions/ and Modules/ (no solid, no certificate), and has Lean list each declaration with the
declarations its type and value name.

**modules.** The nodes are the repository's Lean files (their `import` lines) and every solid's
certificate pieces (names, sizes and imports from Certificates/manifest.json; the pieces are not
needed). Mathlib's and Lean's own modules are left out. Each solid is a cluster laid out by its own
imports, in the smallest circle around it; the clusters of a family are packed in a circle; the
families around the shared library and the definitions. A dot's size grows with its file's size; a
line is coloured by the importing module's purpose (by its file name: see `piece_purpose`).

**library.** The nodes are the declarations written in Definitions/ and Modules/: definitions,
theorems, axioms, opaque constants and structures, not what Lean generates beside them (equation
lemmas, abstracted proofs, matchers, constructors, recursors); a use of a generated constant counts
as a use of what it leads to. Each file is a cluster laid out by its own uses; each directory a
circle of its files; the directories in rows from the definitions (top) to the certificates' formats.

The layouts are force-directed with a fixed seed: a rerun on the same machine draws the same picture byte
for byte. Another processor draws the same clusters, but rounding differences, which the layouts magnify,
can move them (2026-11-25: an AMD VM placed the small families elsewhere than an Intel machine). The
pictures are drawn on black: lines add up (where many cross they are bright), dots on top.
"""
import collections
import json
import math
import random
import re
import subprocess
import sys
from pathlib import Path

# ---------------------------------------------------------------- shared drawing and packing

def font(px, bold=False):
    from PIL import ImageFont
    name = "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf"
    for d in ("/usr/share/fonts/truetype/dejavu/", "/usr/share/fonts/dejavu/", "/usr/share/fonts/TTF/",
              "/Library/Fonts/", "C:/Windows/Fonts/"):
        if Path(d, name).exists():
            return ImageFont.truetype(str(Path(d, name)), max(1, int(px)))
    return ImageFont.load_default(size=max(1, int(px)))


def seed_layouts():
    """igraph's force layouts start from random positions: a fixed seed makes the pictures repeatable."""
    import igraph as ig
    random.seed(1)
    ig.set_random_number_generator(random)


def enclosing(L, iters=400):
    """An approximately smallest circle around the points L (Badoiu-Clarkson): its centre and radius."""
    import numpy as np
    q = L.mean(0)
    for it in range(1, iters):
        far = L[np.argmax(np.linalg.norm(L - q, axis=1))]
        q = q + (far - q) / (it + 1)
    return q, float(np.linalg.norm(L - q, axis=1).max())


def enclosing_circles(c, r, iters=3000):
    """The same for circles (centres c, radii r)."""
    import numpy as np
    q = np.zeros(2)
    for it in range(1, iters):
        far = int(np.argmax(np.linalg.norm(c - q, axis=1) + r))
        u = c[far] - q
        nu = np.linalg.norm(u)
        tip = c[far] + (u / nu if nu > 0 else np.array([1.0, 0.0])) * r[far]
        q = q + (tip - q) / (it + 1)
    return q, float((np.linalg.norm(c - q, axis=1) + r).max())


def pack(r, gap, first=None):
    """Greedy circle packing: `first` (or the largest) at the origin, then the others largest first, each at
    the place tangent to one or two placed circles that grows the enclosing radius least (then the nearest
    to the origin), without overlaps."""
    import numpy as np
    order = list(np.argsort(-r))
    if first is not None:
        order.remove(first)
        order.insert(0, first)
    c = np.zeros((len(r), 2))
    placed = [order[0]]
    for i in order[1:]:
        pc, pr = c[placed], r[placed] + r[i] + gap
        cands = []
        for a in range(len(placed)):
            for t in np.linspace(0, 2 * math.pi, 36, endpoint=False):
                cands.append(pc[a] + pr[a] * np.array([math.cos(t), math.sin(t)]))
            for b in range(a + 1, len(placed)):
                d = np.linalg.norm(pc[b] - pc[a])
                if d == 0 or d > pr[a] + pr[b] or d < abs(pr[a] - pr[b]):
                    continue
                x = (pr[a] ** 2 - pr[b] ** 2 + d * d) / (2 * d)
                h = math.sqrt(max(pr[a] ** 2 - x * x, 0))
                u = (pc[b] - pc[a]) / d
                v = np.array([-u[1], u[0]])
                cands += [pc[a] + x * u + h * v, pc[a] + x * u - h * v]
        C = np.array(cands)
        C = C[(np.linalg.norm(C[:, None, :] - pc[None, :, :], axis=2) >= pr[None, :] - 1e-6).all(1)]
        ext = np.maximum(np.linalg.norm(C, axis=1) + r[i], (np.linalg.norm(pc, axis=1) + r[placed]).max())
        c[i] = C[np.lexsort((np.linalg.norm(C, axis=1), np.round(ext, 3)))[0]]
        placed.append(i)
    return c


def draw_lines(X, E, wgt, W, H, gamma):
    """Every line, one sample per pixel, summed (in chunks, by bincount), then tone-mapped to [0, 1]:
    1 - exp(-1.6 sum), lifted by the power `gamma` (below 1 brightens faint lines)."""
    import numpy as np
    acc = np.zeros((3, H * W))
    for c0 in range(0, len(E), 4000):
        e = slice(c0, c0 + 4000)
        a, b = X[E[e, 0]], X[E[e, 1]]
        n = np.ceil(np.maximum(np.linalg.norm(b - a, axis=1), 1)).astype(int)
        rep = np.repeat(np.arange(len(n)), n)
        t = (np.arange(n.sum()) - np.repeat(np.cumsum(n) - n, n)) / np.repeat(n, n)
        pts = a[rep] + (b[rep] - a[rep]) * t[:, None]
        ix = np.clip(pts.round().astype(np.int64), [0, 0], [W - 1, H - 1])
        flat = ix[:, 1] * W + ix[:, 0]
        for ch in range(3):
            acc[ch] += np.bincount(flat, weights=wgt[e][rep, ch], minlength=H * W)
    return (1 - np.exp(-acc.reshape(3, H, W).transpose(1, 2, 0) * 1.6)) ** gamma


def draw_dots(img, X, rad, col, order, alpha=0.85):
    """Antialiased discs in `order` (the last on top)."""
    import numpy as np
    H, W = img.shape[:2]
    for i in order:
        x, y, rr = X[i, 0], X[i, 1], rad[i]
        x0, x1 = int(max(x - rr - 1, 0)), int(min(x + rr + 2, W))
        y0, y1 = int(max(y - rr - 1, 0)), int(min(y + rr + 2, H))
        if x0 >= x1 or y0 >= y1:
            continue
        yy, xx = np.mgrid[y0:y1, x0:x1]
        m = np.clip(rr + 0.5 - np.hypot(xx - x, yy - y), 0, 1)[:, :, None] * alpha
        img[y0:y1, x0:x1] = img[y0:y1, x0:x1] * (1 - m) + col[i] * m


def save(im, out):
    out = Path(out)
    if out.suffix.lower() == ".webp":
        im.save(out, quality=90, method=6)
    else:
        im.save(out)
    print(f"wrote {out} ({im.width}×{im.height})", file=sys.stderr)


def wrap(t, n):
    out, cur = [], ""
    for w in t.split():
        if cur and len(cur) + 1 + len(w) > n:
            out.append(cur)
            cur = w
        else:
            cur = (cur + " " + w).strip()
    return out + [cur]


# ---------------------------------------------------------------- modules

PURPOSES = [  # key, the legend's label, colour
    ("statement", "Definitions and theorems", (255, 255, 255)),
    ("library", "Shared library", (255, 210, 63)),
    ("proof", "Proof steps", (178, 141, 255)),
    ("far", "Far-field covers", (40, 130, 255)),
    ("exact", "Near-optimum checks", (61, 220, 90)),
    ("weak", "Weak fit at ν", (255, 79, 163)),
    ("nopert", "Nopert covers", (255, 122, 26)),
]
FAMILIES = [("Platonic", "Platonic"), ("Archimedean", "Archimedean"), ("Catalan", "Catalan"), ("Johnson", "Johnson"),
            ("Prism", "Prisms"), ("Antiprism", "Antiprisms"), ("Other", "Other")]


def piece_purpose(stem, nopert):
    """A certificate piece's purpose, by its file name: Root*: the covers away from the optimum (no larger
    copy passes there); a Nopert's Chunk*, Claims* and Group*: its covers (no copy passes); Weak*: the
    weak fit at ν; Shared: proof steps; the rest (Lift, Claim*, Touch, Diameter, Zones, ...): the checks
    near the optimum."""
    k = re.sub(r"\d+", "#", stem)
    if k in ("Root#", "Root#P#"):
        return "far"
    if nopert and k.startswith(("Chunk", "Claims", "Group")):
        return "nopert"
    if k.startswith("Weak"):
        return "weak"
    if k == "Shared":
        return "proof"
    return "exact"


def source_purpose(mod):
    p = mod.split(".")
    if p[0] == "Modules":
        return "library"
    if p[0] == "Polyhedra" and not (len(p) == 4 and p[3] in ("Definition", "Result")):
        return "proof"
    return "statement"   # Definitions/, each solid's Definition and Result, the roots


def solid_name(repo, fam, sol):
    name = json.loads((repo / "Polyhedra" / fam / sol / "data.json").read_text())["name"]
    m = re.fullmatch(r"KAlpha(.+)", sol)
    if m:   # the triakis tetrahedra TT_alpha: alpha from the folder's name (KAlpha13_25, KAlphaSqrt3_3)
        return "Triakis tetrahedron, α = " + m.group(1).replace("Sqrt3", "√3").replace("_", "/")
    return {"Square Pyramid (base [-1,1]^2, apex (0,0,1))": "Square pyramid, height 1"}.get(name, name)


def modules_graph(repo):
    """Every module: name, purpose, bytes, solid ("Family.Folder" or "" for the shared ones); the imports."""
    nodes, edges = {}, []
    files = subprocess.run(["git", "-C", str(repo), "ls-files", "*.lean"], capture_output=True, text=True,
                           check=True).stdout.split()
    imp = re.compile(r"^import\s+(\S+)", re.M)
    for f in files:
        mod = f[:-5].replace("/", ".")
        p = mod.split(".")
        solid = ".".join(p[1:3]) if p[0] == "Polyhedra" and len(p) > 3 else ""
        nodes[mod] = (source_purpose(mod), (repo / f).stat().st_size, solid)
        edges += [(mod, m) for m in imp.findall((repo / f).read_text(encoding="utf-8"))]
    for man in sorted(repo.glob("Polyhedra/*/*/Certificates/manifest.json")):
        fam, sol = man.parts[-4], man.parts[-3]
        nopert = (man.parent.parent / "Proof" / "Nopert.lean").exists()
        for pc in json.loads(man.read_text())["pieces"]:
            mod = f"Polyhedra.{fam}.{sol}.Certificates.{pc['file'][:-5]}"
            nodes[mod] = (piece_purpose(pc["file"][:-5], nopert), pc["bytes"], f"{fam}.{sol}")
            edges += [(mod, m) for m in pc["imports"]]
    unresolved = sorted({b for _, b in edges if b not in nodes and not b.startswith(("Mathlib", "Std", "Lean", "Init"))})
    if unresolved:
        sys.exit(f"imports of the project that no file or piece has: {unresolved[:5]}")
    return nodes, [(a, b) for a, b in edges if b in nodes]


def modules(repo, out, W):
    import numpy as np
    import igraph as ig
    from PIL import Image, ImageDraw
    seed_layouts()
    nodes, edges = modules_graph(repo)
    names = sorted(nodes)
    idx = {n: i for i, n in enumerate(names)}
    solids = sorted({v[2] for v in nodes.values() if v[2]})
    S = len(solids)
    keys = [k for k, _, _ in PURPOSES]
    pur = np.array([keys.index(nodes[n][0]) for n in names])
    size = np.array([nodes[n][1] for n in names], dtype=float)
    grp = np.array([solids.index(nodes[n][2]) if nodes[n][2] else S for n in names])  # the shared core: S
    E = np.array([[idx[a], idx[b]] for a, b in edges])
    N = len(names)
    fam = [s.split(".")[0] for s in solids]
    assert set(fam) <= {f for f, _ in FAMILIES}, sorted(set(fam))
    print(f"{N:,} modules, {size.sum() / 1e9:.1f} GB, {len(E):,} imports, {S} solids", file=sys.stderr)

    # each cluster by its own imports: radius about sqrt(count), the outer 3% pulled to the rim, then
    # centred on the smallest circle around it
    local, rc = np.zeros((N, 2)), np.zeros(S + 1)
    inside = grp[E[:, 0]] == grp[E[:, 1]]
    for k in range(S + 1):
        m = np.flatnonzero(grp == k)
        if len(m) > 1:
            loc = {v: i for i, v in enumerate(m)}
            ek = [(loc[a], loc[b]) for a, b in E[inside & (grp[E[:, 0]] == k)]]
            L = np.array(ig.Graph(n=len(m), edges=ek).layout_fruchterman_reingold(niter=400, grid=len(m) > 1000).coords)
            L -= L.mean(0)
            rad = math.sqrt(len(m)) + 2.0
            L = L / (np.percentile(np.hypot(*L.T), 97) or 1.0) * (rad - 1.0)
            r = np.hypot(*L.T)
            L *= (np.minimum(r, 1.08 * rad) / np.maximum(r, 1e-9))[:, None]
            q, _ = enclosing(L)
            local[m] = L - q
        rc[k] = max(np.linalg.norm(local[m], axis=1).max(), 1.5)
    slot = rc + 0.8
    # the families: each a packed circle of its clusters; the circles packed around the shared core
    centre, fams = np.zeros((S + 1, 2)), []
    for f, label in FAMILIES:
        ks = [k for k in range(S) if fam[k] == f]
        c = pack(slot[ks], 0.6)
        q, R = enclosing_circles(c, slot[ks])
        centre[ks] = c - q
        fams.append((label, len(ks), ks, R + 3.0))
    outer = pack(np.array([slot[S] + 2.0] + [x[3] for x in fams]), 10.0, first=0)
    for j, (_, _, ks, _) in enumerate(fams):
        centre[ks] += outer[j + 1]
    # the whole picture turned about the core to its widest (the least height over width): a page's shape
    FR = np.array([x[3] for x in fams])

    def turn(a):
        t = math.radians(a)
        return np.array([[math.cos(t), -math.sin(t)], [math.sin(t), math.cos(t)]])

    def aspect(a):
        c = outer[1:] @ turn(a).T
        ext = (c + FR[:, None]).max(0) - (c - FR[:, None]).min(0)
        return round(ext[1] / ext[0], 6)
    T = turn(min(range(0, 360, 2), key=aspect))
    centre, local = centre @ T.T, local @ T.T
    P = local + centre[grp]

    # the frame: the family circles across the width; their titles, the title and the legend above
    s = W / 2400
    FC = outer[1:] @ T.T
    lo, hi = (FC - FR[:, None]).min(0), (FC + FR[:, None]).max(0)
    side = 70 * s
    scale = (W - 2 * side) / (hi - lo)[0]
    lo[1] -= 48 * s / scale
    span = hi - lo
    top = 380 * s
    H = int(top + span[1] * scale + 60 * s)
    mid = (lo + hi) / 2
    off = np.array([W / 2, top + span[1] * scale / 2])
    X = (P - mid) * scale + off
    COL = np.array([c for _, _, c in PURPOSES], dtype=float) / 255
    same = grp[E[:, 0]] == grp[E[:, 1]]
    wgt = COL[pur[E[:, 0]]] * np.where(same, 0.035, 0.005)[:, None] / (W / 1800)
    img = draw_lines(X, E, wgt, W, H, 0.75)
    rad = np.clip(0.3 + 0.32 * np.log10(np.maximum(size, 1) / 2e3), 0.3, 1.5) * W / 2400
    draw_dots(img, X, rad, COL[pur], np.argsort(size, kind="stable"))
    im = Image.fromarray((np.clip(img, 0, 1) * 255).astype(np.uint8)).convert("RGBA")
    d = ImageDraw.Draw(im)
    for (label, n, _, R), c in zip(fams, FC):
        cx, cy = (c - mid) * scale + off
        R *= scale
        d.ellipse((cx - R, cy - R, cx + R, cy + R), outline=(105, 105, 105), width=max(1, int(2 * s)))
        t = f"{label} ({n})"
        w = d.textlength(t, font=font(30 * s, True))
        d.text((cx - w / 2, cy - R - 40 * s), t, font=font(30 * s, True), fill=(235, 235, 235),
               stroke_width=max(1, int(3 * s)), stroke_fill=(0, 0, 0))
    # labels on the clusters large enough for one, sized with the cluster, half transparent
    lay = Image.new("RGBA", im.size, (0, 0, 0, 0))
    dl = ImageDraw.Draw(lay)
    count = np.bincount(grp, minlength=S + 1)
    for k in range(S + 1):
        rr = rc[k] * scale
        name = "Shared library and definitions" if k == S else solid_name(repo, *solids[k].split("."))
        lines = wrap(name, 14)
        widest = max(dl.textlength(t, font=font(100, True)) for t in lines)
        px = min(0.19 * rr, 40 * s, 1.75 * rr * 100 / widest)
        if k == S:
            px = max(px, 16 * s)   # the shared core: small, but named
        if px < 11 * s:
            continue
        n = count[k]
        lines.append((f"{n / 1000:.1f}k" if n >= 1000 else str(n)) + " modules")
        cx, cy = (centre[k] - mid) * scale + off
        lh = px * 1.18
        y = cy - lh * len(lines) / 2 if k < S else cy - rr - 4 * s - lh * len(lines)
        for j, t in enumerate(lines):
            last = j == len(lines) - 1
            f = font(px * 0.8) if last else font(px, True)
            dl.text((cx - dl.textlength(t, font=f) / 2, y + j * lh), t, font=f, fill=(255, 255, 255, 120 if last else 150))
    im = Image.alpha_composite(im, lay).convert("RGB")
    d = ImageDraw.Draw(im)
    d.text((48 * s, 40 * s), f"Rupertness and Nieuwland numbers of {S} polyhedra, in Lean", font=font(54 * s, True), fill=(255, 255, 255))
    d.text((50 * s, 112 * s), f"{N:,} modules, {size.sum() / 1e9:.0f} GB", font=font(30 * s), fill=(190, 190, 190))
    d.text((50 * s, 150 * s), f"{len(E):,} imports", font=font(30 * s), fill=(190, 190, 190))
    counts = np.bincount(pur, minlength=len(PURPOSES))
    gb = np.bincount(pur, weights=size, minlength=len(PURPOSES)) / 1e9
    fl, fx = font(22 * s), font(20 * s)
    rows = [(label, f"{counts[i]:,}" + (f", {gb[i]:.0f} GB" if gb[i] >= 1 else "")) for i, (_, label, _) in enumerate(PURPOSES)]
    colw = max(d.textlength(a + "  ", font=fl) + d.textlength(b, font=fx) for a, b in rows) + 70 * s
    for i, (label, extra) in enumerate(rows):
        x0, y0 = 50 * s + (i // 4) * colw, 205 * s + (i % 4) * 34 * s
        d.ellipse((x0, y0 + 6 * s, x0 + 16 * s, y0 + 22 * s), fill=PURPOSES[i][2])
        d.text((x0 + 30 * s, y0), label, font=fl, fill=(225, 225, 225))
        d.text((x0 + 30 * s + d.textlength(label + "  ", font=fl), y0 + 1 * s), extra, font=fx, fill=(150, 150, 150))
    save(im, out)


# ---------------------------------------------------------------- declarations

DUMP = r"""
open Lean
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
-- one line per constant of the library's modules: D, name, module, kind, flags (i internal, a auxiliary
-- recursor, n noConfusion, m matcher; - none), the library constants its type names, those its value
-- names, and how many other (Mathlib's, Lean's) constants it names
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name :=
    match env.getModuleIdxFor? n with
    | some i => let m := mods[i.toNat]!
                if (`Definitions).isPrefixOf m || (`Modules).isPrefixOf m then some m else none
    | none => none
  let rows := env.constants.fold (init := #[]) fun acc c ci =>
    match modOf c with
    | none => acc
    | some m =>
      let tu := ci.type.getUsedConstants
      let vu := (ci.value?.map (·.getUsedConstants)).getD #[]
      let lib (xs : Array Name) := " ".intercalate ((xs.filter fun d => (modOf d).isSome && d != c).toList.map toString)
      let other := ((tu ++ vu).filter fun d => (modOf d).isNone).toList.eraseDups.length
      let flags := (if c.isInternal then "i" else "") ++ (if isAuxRecursor env c then "a" else "") ++
        (if isNoConfusion env c then "n" else "") ++ (if Meta.isMatcherCore env c then "m" else "")
      acc.push s!"D\t{c}\t{m}\t{kindOf ci}\t{if flags.isEmpty then "-" else flags}\t{lib tu}\t{lib vu}\t{other}"
  for r in rows.qsort (· < ·) do IO.println r
"""


def declarations(repo, out):
    mods = sorted(str(p.relative_to(repo).with_suffix("")).replace("/", ".")
                  for d in ("Definitions", "Modules") for p in (repo / d).rglob("*.lean"))
    print(f"{len(mods)} library modules", file=sys.stderr)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=repo, check=True)
    subprocess.run(["lake", "build"] + ["+" + m for m in mods], cwd=repo, check=True)
    dump = repo / ".lake" / "graphs_dump.lean"
    dump.write_text("".join(f"import {m}\n" for m in mods) + DUMP)
    with open(out, "w") as f:
        subprocess.run(["lake", "env", "lean", str(dump.relative_to(repo))], cwd=repo, stdout=f, check=True)
    n = sum(1 for line in open(out) if line.startswith("D\t"))
    if not n:
        sys.exit("the dump listed no declarations")
    print(f"{n:,} constants in {out}", file=sys.stderr)


# ---------------------------------------------------------------- library

GENERATED = re.compile(r"^(eq_\d+|eq_def|proof_\d+|match_\d+|_.*|sizeOf_spec|injEq|inj|noConfusionType|below|brecOn|"
                       r"binductionOn|ibelow|recOn|casesOn|ctorIdx|term.*|«term.*)$")
ROWS = [  # label, colour, directories (a row's order is refined by where its uses lead)
    ("Definitions", (255, 255, 255), ["Definitions"]),
    ("Results", (255, 210, 63), ["Rupert", "Nieuwland"]),
    ("Theory", (178, 141, 255), ["NoFit", "Pose", "Identity", "System", "Root"]),
    ("Checks", (61, 220, 90), ["Check.Leaf", "Check.Sign", "Check.Polynomial", "Check.Chart", "Check.Number"]),
    ("Certificates", (40, 130, 255), ["Certificate"]),
]
SHOW = {"Check.Leaf": "Leaves", "Check.Sign": "Signs", "Check.Polynomial": "Polynomials", "Check.Chart": "Charts",
        "Check.Number": "Numbers", "NoFit": "No fit", "System": "Systems", "Root": "Roots", "Identity": "Symmetries",
        "Pose": "Poses", "Certificate": "Certificates", "Definitions": "Definitions", "Rupert": "Rupert",
        "Nieuwland": "Nieuwland"}


def library_graph(tsv):
    """The declarations written in the source and their uses (A -> B: A's type or value names B, or names a
    generated constant that leads to B through generated ones only)."""
    rows = {}
    for line in open(tsv, encoding="utf-8"):
        p = line.rstrip("\n").split("\t")
        if p[0] == "D":
            name, mod, kind, flags, tu, vu = p[1:7]
            rows[name] = (mod, kind, flags, set((tu + " " + vu).split()))
    keep = {n for n, (_, k, f, _) in rows.items()
            if k in ("def", "thm", "axiom", "opaque", "induct") and f == "-" and not GENERATED.match(n.rsplit(".", 1)[-1])}
    reach = {}

    def through(x, stack=()):
        if x not in reach:
            out = set()
            if x not in stack:
                for y in rows[x][3]:
                    out |= {y} if y in keep else (through(y, stack + (x,)) if y in rows else set())
            reach[x] = out
        return reach[x]

    sys.setrecursionlimit(100000)
    names = sorted(keep)
    idx = {n: i for i, n in enumerate(names)}
    edges = sorted({(idx[n], idx[t]) for n in names for y in rows[n][3]
                    for t in ({y} if y in keep else (through(y) if y in rows else set())) if t != n})
    return names, [rows[n][0] for n in names], edges


def library(tsv, out, W):
    import numpy as np
    import igraph as ig
    from PIL import Image, ImageDraw
    seed_layouts()
    names, mods, edges = library_graph(tsv)
    N, E = len(names), np.array(edges)
    print(f"{N:,} declarations, {len(E):,} uses", file=sys.stderr)

    def group(m):
        p = m.split(".")
        if p[0] == "Definitions":
            return "Definitions"
        return "Check." + p[2] if len(p) >= 3 and p[1] == "Check" else ".".join(p[1:2]) or m
    grp = [group(m) for m in mods]
    row_of = {g: i for i, (_, _, gs) in enumerate(ROWS) for g in gs}
    if set(grp) - set(row_of):
        sys.exit(f"directories without a row: {sorted(set(grp) - set(row_of))}")
    members, chunks = collections.defaultdict(list), collections.defaultdict(list)
    for i, (g, m) in enumerate(zip(grp, mods)):
        members[g].append(i)
        chunks[m].append(i)
    # each file a chunk, laid out by its own uses (a hidden hub, tied weakly to all, keeps the unconnected
    # ones in it), its radius about sqrt(count); each directory a packed circle of its files
    local, crad = np.zeros((N, 2)), {}
    for m, ids in chunks.items():
        if len(ids) == 1:
            L = np.zeros((1, 2))
        else:
            loc = {v: j for j, v in enumerate(ids)}
            ek = sorted({tuple(sorted((loc[a], loc[b]))) for a, b in E if a in loc and b in loc and a != b})
            g = ig.Graph(n=len(ids) + 1, edges=ek + [(j, len(ids)) for j in range(len(ids))])
            L = np.array(g.layout_fruchterman_reingold(niter=500, weights=[1.0] * len(ek) + [0.08] * len(ids),
                                                       grid=len(ids) > 800).coords)[:len(ids)]
        med = np.median(L, 0)
        r0 = np.linalg.norm(L - med, axis=1)
        lim = np.percentile(r0, 95) * 1.15 if len(ids) > 3 else r0.max()
        L = med + (L - med) * (np.minimum(r0, lim) / np.maximum(r0, 1e-9))[:, None]
        q, R = enclosing(L) if len(ids) > 1 else (L[0], 0.0)
        crad[m] = 0.62 * math.sqrt(len(ids)) + 0.6
        local[ids] = (L - q) / (R or 1.0) * crad[m]
    rad = {}
    for g, ids in members.items():
        ms = sorted({mods[i] for i in ids})
        r = np.array([crad[m] for m in ms])
        c = pack(r, 2.6) if len(ms) > 1 else np.zeros((1, 2))
        q, R = enclosing(np.concatenate([c + r[:, None] * np.array([[math.cos(t), math.sin(t)]])
                                         for t in np.linspace(0, 2 * math.pi, 24, endpoint=False)]))
        for m, cc in zip(ms, c - q):
            local[chunks[m]] += cc
        rad[g] = R + 2.0
    # the rows, top to bottom; in a row the directories side by side, ordered by the mean place of what
    # they use in the rows above
    GAP, cx, rows_y, y = 14.0, {}, [], 0.0
    for i, (_, _, gs) in enumerate(ROWS):
        if i:
            gs = sorted(gs, key=lambda g: np.mean([cx[grp[b]] for a, b in E if grp[a] == g and grp[b] in cx] or [0.0]))
        x = -(sum(2 * rad[g] for g in gs) + GAP * (len(gs) - 1)) / 2
        h = max(2 * rad[g] for g in gs)
        for g in gs:
            cx[g] = x + rad[g]
            x += 2 * rad[g] + GAP
            local[members[g]] += [cx[g], y + h / 2]
        rows_y.append((y, h))
        y += h + 2.2 * GAP
    lo, hi = local.min(0), local.max(0)

    s = W / 2400
    side, top = 90 * s, 250 * s
    scale = (W - 2 * side) / (hi - lo)[0]
    H = int(top + (hi - lo)[1] * scale + 80 * s)
    X = (local - lo) * scale + [side, top]
    COL = np.array([c for _, c, _ in ROWS], dtype=float) / 255
    row = np.array([row_of[g] for g in grp])
    img = draw_lines(X, E, COL[row[E[:, 0]]] * (0.014 / s), W, H, 0.85)
    indeg = np.bincount(E[:, 1], minlength=N)
    draw_dots(img, X, np.clip(0.9 + 0.55 * np.log1p(indeg), 0.9, 4.0) * s, COL[row], np.argsort(indeg, kind="stable"))
    im = Image.fromarray((np.clip(img, 0, 1) * 255).astype(np.uint8)).convert("RGBA")
    lay = Image.new("RGBA", im.size, (0, 0, 0, 0))
    dl = ImageDraw.Draw(lay)
    for g, ids in members.items():
        gx, gy = (np.array([cx[g], rows_y[row_of[g]][0] + rows_y[row_of[g]][1] / 2]) - lo) * scale + [side, top]
        rr = rad[g] * scale
        dl.ellipse((gx - rr, gy - rr, gx + rr, gy + rr), outline=(120, 120, 120, 200), width=max(1, int(2 * s)))
        t1, t2 = SHOW.get(g, g), f"  {len(ids):,}"
        px = float(np.clip(rr * 0.16, 17 * s, 34 * s))
        w1, w2 = dl.textlength(t1, font=font(px, True)), dl.textlength(t2, font=font(px * 0.8))
        yl = gy - rr - px * 1.5
        dl.text((gx - (w1 + w2) / 2, yl), t1, font=font(px, True), fill=(255, 255, 255, 200))
        dl.text((gx - (w1 + w2) / 2 + w1, yl + px * 0.15), t2, font=font(px * 0.8), fill=(255, 255, 255, 150))
    im = Image.alpha_composite(im, lay).convert("RGB")
    d = ImageDraw.Draw(im)
    d.text((48 * s, 40 * s), "The shared library", font=font(46 * s, True), fill=(255, 255, 255))
    d.text((50 * s, 104 * s), f"{N:,} definitions and theorems", font=font(28 * s), fill=(190, 190, 190))
    d.text((50 * s, 140 * s), f"{len(E):,} dependencies", font=font(28 * s), fill=(190, 190, 190))
    for i, (label, c, gs) in enumerate(ROWS):
        d.text((side * 0.5, (rows_y[i][0] - lo[1]) * scale + top - 4 * s),
               f"{label}  ({sum(len(members[g]) for g in gs):,})", font=font(21 * s, True), fill=c)
    save(im, out)


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) in (3, 4) and a[0] == "modules":
        modules(Path(a[1]).resolve(), a[2], int(a[3]) if len(a) == 4 else 3000)
    elif len(a) == 3 and a[0] == "declarations":
        declarations(Path(a[1]).resolve(), Path(a[2]).resolve())
    elif len(a) in (3, 4) and a[0] == "library":
        library(a[1], a[2], int(a[3]) if len(a) == 4 else 3000)
    else:
        sys.exit(__doc__)
