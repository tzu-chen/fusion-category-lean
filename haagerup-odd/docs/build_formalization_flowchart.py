"""Build dark and light self-contained SVGs and interactive proof maps.

Uses only the stdlib. Light outputs use the formalization_flowchart_light stem.

Run from the project root:
    python docs/build_formalization_flowchart.py
Export the SVG with rsvg-convert for PDF/PNG.
"""

from html import escape
from pathlib import Path
import json
import re

OUT = Path(__file__).resolve().parent
WIDTH, HEIGHT = 1400, 1048
COLORS = {
    "gamma": ("#123941", "#48b4c9", "#abe0e9"),
    "bridge": ("#144550", "#69d0e3", "#c6f0f5"),
    "analysis": ("#392b12", "#e6b353", "#efd291"),
    "algebra": ("#20372b", "#78bd94", "#bee3cc"),
    "result": ("#42182f", "#ed67ae", "#f4bddc"),
}

# Translate the shared SVG/HTML palette in one pass, so both versions retain
# exactly the same proof content, layout, and interactions. Each stage keeps
# its hue, with pale card fills and dark text/lines on the light canvas.
LIGHT_PALETTE = {
    # Stage cards: fill, outline/arrow, label.
    "#123941": "#eaf6f8", "#48b4c9": "#207b8b", "#abe0e9": "#145461",
    "#144550": "#d9f0f4", "#69d0e3": "#176b80", "#c6f0f5": "#104c5c",
    "#392b12": "#fff4dc", "#e6b353": "#996719", "#efd291": "#744d11",
    "#20372b": "#eaf4eb", "#78bd94": "#487e56", "#bee3cc": "#295d37",
    "#42182f": "#fce9f3", "#ed67ae": "#b13b78", "#f4bddc": "#882857",
    # Page, canvas, section fills, borders, and controls.
    "#101318": "#f4f3ef", "#14171c": "#ffffff", "#e8e5df": "#263238",
    "#191f24": "#f3f9fa", "#29373d": "#ccdde1",
    "#1c2026": "#fcf9f1", "#303239": "#e2ddcf",
    "#1b2422": "#f3f8f3", "#314139": "#cfddd1",
    "#303640": "#d6dce0", "#39424e": "#c7d0d6", "#2a323b": "#e9eef1",
    "#c9d3df": "#344650", "#68bfd2": "#176b80", "#31432908": "#2632380c",
    # Section headings, annotations, captions, and source links.
    "#78c6d6": "#216473", "#ddbd7a": "#806020", "#a2d4b5": "#376746",
    "#c7d9de": "#365761", "#8eabb3": "#506b73", "#d2c6a9": "#6b5833",
    "#a9b4c2": "#53616d", "#b5bcc5": "#4d5b67", "#9faab7": "#5c6670",
    "#b8c1cd": "#4d5b67", "#829aa3": "#5b6f76", "#99a5b4": "#63707b",
    "#80cbdc": "#176b80", "#939faf": "#63707b",
}


def light_palette(markup):
    return re.sub(r"#[0-9a-f]{8}\b|#[0-9a-f]{6}\b",
                  lambda match: LIGHT_PALETTE.get(match[0], match[0]), markup)


def source(file, line, theorem):
    return {"file": file, "line": line, "theorem": theorem}


NODES = [
    dict(id="integral", kind="gamma", x=54, y=164, w=360, h=82,
         title="Construct hyperbolic γ", lines=["Regularized BSS integral", "Finite-product continuation"],
         detail="Start with an explicit, absolutely convergent regularized integral on the fundamental strip. Prove holomorphy and extend the function by finite products of its shift factors.",
         sources=[source("Analytic/GammaIntegral.lean", 340, "GammaIntegral.integrableOn_integrand"), source("Analytic/GammaContinuation.lean", 545, "GammaContinuation.gamma")]),
    dict(id="core", kind="gamma", x=520, y=164, w=360, h=82,
         title="Gamma foundation", lines=["Shifts · reflection · poles & residues", "Uniform growth estimates"],
         detail="Prove the local identities, exact pole and zero sets, simple residues for irrational period ratios, positivity, and the uniform ratio estimates needed for contour decay. These results supply HypGammaCore.",
         sources=[source("Analytic/GammaCore.lean", 27, "GammaContinuation.core")]),
    dict(id="two_gamma", kind="gamma", x=986, y=164, w=360, h=82,
         title="Two-gamma transform", lines=["Dual shifts + sech normalization", "Full crossed-pole evaluation"],
         detail="Local incommensurable periods determine the symmetric Fourier transform. The elementary sech integral fixes its normalization, and a finite shift argument extends the evaluation to the full residue-corrected domain.",
         sources=[source("Analytic/GammaFourierEvaluation.lean", 52, "symmetricTransform_evaluation"), source("Analytic/GammaTwoGammaInterface.lean", 62, "two_gamma_explicit")]),
    dict(id="four_gamma", kind="gamma", x=520, y=282, w=360, h=82,
         title="Four-gamma contours", lines=["Residue corrections + symmetries", "Four-term identity"],
         detail="Define K₄ by an actual vertical integral with finite residue corrections. Prove line independence, evenness, the swap identity, and the four-term relation. Generalized residues retain coincident poles. The contour machinery from this stage also supports Euler; the four-term relation itself is not used to prove Euler.",
         sources=[source("Analytic/GammaK4Interface.lean", 32, "K4_line_explicit"), source("Analytic/GammaK4FourTermInterface.lean", 17, "K4_four_term")]),
    dict(id="euler", kind="gamma", x=986, y=282, w=360, h=82,
         title="Euler transformation", lines=["Fourier insertion + Fubini", "Continuation with moving pole clusters"],
         detail="Prove Euler on an initial open domain by absolutely integrable Fourier insertion and Fubini. Fixed contour loops around moving pole clusters establish holomorphy, and a connected complex scaling domain extends the identity throughout the required convergent, non-pinched parameter range.",
         sources=[source("Analytic/GammaK4EulerInterface.lean", 17, "GammaK4Contour.K4_euler")]),
    dict(id="interface", kind="bridge", x=520, y=396, w=360, h=70,
         title="Full gamma interface", lines=["Specialized periods and analytic identities", "ruijsenaarsHypGamma"],
         detail="Assemble every HypGamma field from the explicit gamma construction and its integral identities. Specialize to ω₁ = d + 1 and ω₂ = 1 + 1/d. This interface supplies the analytic input throughout the coefficient proof, including direct uses in the column, product, and restricted Fourier transforms.",
         sources=[source("Analytic/GammaConstruction.lean", 23, "GammaContinuation.hypGamma"), source("Analytic/GammaConstruction.lean", 37, "ruijsenaarsHypGamma")]),
    dict(id="samples", kind="analysis", x=520, y=540, w=360, h=76,
         title="Sample the coefficients", lines=["F(z) = 1 / γ(ω₂ + z)", "Explicit odd-order matrix"],
         detail="The specialized gamma gives the samples W and the concrete coefficient data, including W₀ = −1 and Wₐ W₋ₐ = δ for nonzero a. The full gamma interface supplies analytic identities throughout the Fourier stage.",
         sources=[source("Analytic/Sampling.lean", 366, "Concrete.toCoeffData")]),
    dict(id="quadratics", kind="analysis", x=54, y=650, w=360, h=76,
         title="Quadratic identities", lines=["Column Fourier transform", "Q = 0"],
         detail="The column interpolation formula and the two-gamma transform determine the discrete Fourier transform of the samples. The reciprocal Fourier relation then proves all quadratic identities.",
         sources=[source("Analytic/ColumnFourier.lean", 42, "column_fourier"), source("Analytic/ColumnFourier.lean", 391, "Q_eq_zero")]),
    dict(id="products", kind="analysis", x=986, y=540, w=360, h=76,
         title="Product transforms", lines=["Left product · right product", "Negative-column transform"],
         detail="Contour sampling gives the two product transforms and the negative-column transform, including crossed poles, double poles, and exceptional sample corrections.",
         sources=[source("Analytic/LeftProduct.lean", 1206, "left_product"), source("Analytic/RightProduct.lean", 1753, "right_product"), source("Analytic/NegColumn.lean", 372, "neg_column")]),
    dict(id="restricted", kind="analysis", x=986, y=650, w=360, h=76,
         title="Restricted Fourier vanishing", lines=["Euler + four-term cancellation", "RestrictedFourier"],
         detail="Combine the product transforms with the proved Euler and four-term identities. Their coefficients cancel to give the restricted Fourier vanishing statement used in the algebraic completion.",
         sources=[source("Analytic/Restricted.lean", 865, "bracket_zero"), source("Analytic/Cubics.lean", 70, "restricted_fourier")]),
    dict(id="cubics", kind="algebra", x=520, y=806, w=360, h=76,
         title="All cubic identities", lines=["Boundary cases · interpolation · induction", "Normal forms + matrix reflection"],
         detail="Quadratics and restricted Fourier vanishing feed the ordered induction. Boundary and collision identities handle degenerate cases; normal forms and reflection by matrix inversion extend the result to every cubic identity.",
         sources=[source("Completion.lean", 321, "CoeffData.C_all")]),
    dict(id="eg", kind="algebra", x=520, y=914, w=360, h=76,
         title="All Evans–Gannon equations", lines=["Quartics from quadratics + cubics", "Linear identities + final assembly"],
         detail="The quartic residual is a contraction of cubic and quadratic residuals. Combine its vanishing with the proved linear, quadratic, and cubic identities to obtain the complete EGEquations structure.",
         sources=[source("Quartic.lean", 97, "Kq_eq_zero"), source("Completion.lean", 357, "EGEquations_of"), source("Analytic/Cubics.lean", 92, "EGEquations_concrete")]),
    dict(id="odd", kind="result", x=986, y=914, w=360, h=76,
         title="Every odd n", lines=["Explicit complex coefficient data", "Unconditional existence theorem"],
         detail="exists_EGEquations_odd requires only Odd n. The theorem covers every odd natural number, including n = 1, and supplies concrete complex coefficient data satisfying all Evans–Gannon equations. Categorical reconstruction is outside this formalization.",
         sources=[source("Analytic/GammaConstruction.lean", 52, "EGEquations_ruijsenaars"), source("Analytic/GammaConstruction.lean", 58, "exists_EGEquations_odd")]),
]

# The screenshot uses uppercase stage labels and monospace Lean names.
PRESENTATION = {
    "integral": ("CONSTRUCTION · REGULARIZED INTEGRAL", "GammaContinuation.gamma", "BSS integral · finite-product continuation"),
    "core": ("CORE · SHIFTS, POLES & GROWTH", "GammaContinuation.core", "Reflection · residues · uniform ratio bounds"),
    "two_gamma": ("TWO-GAMMA · FOURIER EVALUATION", "two_gamma_explicit", "Dual shifts · sech normalization · crossed poles"),
    "four_gamma": ("FOUR-GAMMA · CORRECTED CONTOURS", "K4_line_explicit · K4_four_term", "Residues · line independence · evenness · swap"),
    "euler": ("EULER · PARAMETER CONTINUATION", "K4_euler", "Fourier insertion · Fubini · moving pole clusters"),
    "interface": ("FULL INTERFACE · SPECIALIZED PERIODS", "ruijsenaarsHypGamma", "Analytic input for the coefficient construction"),
    "samples": ("SAMPLING · CONCRETE COEFFICIENTS", "Concrete.toCoeffData", "F(z) = 1/γ(ω₂ + z) · explicit odd-order matrix"),
    "quadratics": ("COLUMN FOURIER · QUADRATICS", "column_fourier · Q_eq_zero", "All quadratic residuals vanish"),
    "products": ("PRODUCTS · CONTOUR SAMPLING", "left_product · right_product", "Product transforms + negative-column transform"),
    "restricted": ("RESTRICTED · FOURIER VANISHING", "restricted_fourier", "Euler + four-term identity cancel the bracket"),
    "cubics": ("COMPLETION · ALL CUBICS", "CoeffData.C_all", "Boundary cases · interpolation · induction"),
    "eg": ("COMPLETION · EVANS–GANNON", "EGEquations_concrete", "Linear, quadratic, cubic and quartic identities"),
    "odd": ("MAIN THEOREM · EVERY ODD n", "exists_EGEquations_odd", "Explicit complex coefficient data · unconditional"),
}

# Selected dependencies between grouped proof stages. Shared inputs and some
# transitive arrows are omitted; the gamma interface feeds the full Fourier stage.
EDGES = [
    ("integral", "core", "M 414 205 H 511"),
    ("core", "two_gamma", "M 880 205 H 977"),
    ("core", "four_gamma", "M 700 246 V 273"),
    ("two_gamma", "euler", "M 1166 246 V 273"),
    ("four_gamma", "euler", "M 880 323 H 977"),
    ("four_gamma", "interface", "M 700 364 V 387"),
    ("euler", "interface", "M 1166 364 V 417 Q 1166 431 1152 431 H 889"),
    ("interface", "samples", "M 700 466 V 531"),
    ("samples", "quadratics", "M 590 616 V 619 Q 590 634 575 634 H 249 Q 234 634 234 641"),
    ("samples", "products", "M 880 578 H 977"),
    ("products", "restricted", "M 1166 616 V 641"),
    ("quadratics", "cubics", "M 414 688 H 440 Q 454 688 454 702 V 830 Q 454 844 468 844 H 511"),
    ("restricted", "cubics", "M 1166 726 V 830 Q 1166 844 1152 844 H 889"),
    ("cubics", "eg", "M 700 882 V 905"),
    ("eg", "odd", "M 880 952 H 977"),
]


def text(x, y, value, size=14, color="#52625b", weight=400, anchor="start", extra=""):
    return f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" font-weight="{weight}" text-anchor="{anchor}" {extra}>{escape(value)}</text>'


def node_svg(n):
    fill, stroke, ink = COLORS[n["kind"]]
    x, y, w, h = (n[k] for k in ("x", "y", "w", "h"))
    label, code, caption = PRESENTATION[n["id"]]
    pieces = [f'<g class="node {n["kind"]}" id="node-{n["id"]}" data-node="{n["id"]}" tabindex="0" role="button" aria-label="{escape(n["title"])}" aria-pressed="false">',
              f'<title>{escape(n["title"])}</title><desc>{escape(n["detail"])}</desc>',
              f'<rect class="card" x="{x}" y="{y}" width="{w}" height="{h}" rx="3" fill="{fill}" stroke="{stroke}" stroke-width="{2 if n["kind"] in ("bridge", "result") else 1.5}"/>']
    pieces.append(text(x + 16, y + 18, label, 10, ink, 600, extra='letter-spacing=".7"'))
    pieces.append(text(x + 16, y + 42, code, 16, ink, 500,
                       extra='font-family="Adwaita Mono, DejaVu Sans Mono, monospace"'))
    pieces.append(text(x + 16, y + 63, caption, 12, "#b5bcc5"))
    pieces.append('</g>')
    return ''.join(pieces)


def build_svg():
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" height="{HEIGHT}" viewBox="0 0 {WIDTH} {HEIGHT}" role="img" aria-labelledby="chart-title chart-desc">',
           '<title id="chart-title">The complete odd-order Evans–Gannon formalization</title>',
           '<desc id="chart-desc">Thirteen grouped proof stages, from the explicit hyperbolic gamma integral through its identities, finite Fourier analysis, and algebraic completion to the unconditional theorem for every odd natural number. Cyan marks gamma results; amber marks finite Fourier analysis; green marks algebraic completion; magenta marks the final theorem. Arrows show selected mathematical dependencies. The gamma interface supplies analytic input throughout the Fourier stage.</desc>',
           '<defs>']
    for name in ("gamma", "analysis", "algebra", "result"):
        color = COLORS[name][1]
        out.append(f'<marker id="arrow-{name}" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="5.5" markerHeight="5.5" orient="auto"><path d="M 1 1 L 9 5 L 1 9 Z" fill="{color}"/></marker>')
    out.extend(['</defs><g font-family="Adwaita Sans, DejaVu Sans, sans-serif">',
           f'<rect width="{WIDTH}" height="{HEIGHT}" fill="#14171c"/>',
           text(54, 48, "From the Gamma Integral to Evans–Gannon", 29, "#e8e5df", 600,
                extra='font-family="DejaVu Serif, Georgia, serif"'),
           text(54, 79, "From the hyperbolic gamma construction to the Evans–Gannon equations for every odd n.", 14, "#a9b4c2"),
           text(1346, 45, "LEAN 4 + MATHLIB", 11, "#a9b4c2", 600, "end", 'letter-spacing="1"'),
           '<rect x="28" y="113" width="1344" height="371" rx="4" fill="#191f24" stroke="#29373d"/>',
           text(54, 140, "01  GAMMA FOUNDATION", 11, "#78c6d6", 600, extra='letter-spacing="1.3"'),
           text(1346, 140, "INTEGRAL · CONTINUATION · TRANSFORM IDENTITIES", 10, "#78c6d6", 600, "end", 'letter-spacing=".8"'),
           '<rect x="28" y="505" width="1344" height="240" rx="4" fill="#1c2026" stroke="#303239"/>',
           text(54, 532, "02  FINITE FOURIER ANALYSIS", 11, "#ddbd7a", 600, extra='letter-spacing="1.2"'),
           '<rect x="28" y="766" width="1344" height="238" rx="4" fill="#1b2422" stroke="#314139"/>',
           text(54, 793, "03  ALGEBRAIC COMPLETION", 11, "#a2d4b5", 600, extra='letter-spacing="1.2"'),
           text(74, 302, "Hyperbolic gamma and its identities", 16, "#c7d9de", 500),
           text(74, 328, "An explicit integral and contour transformations.", 12.5, "#8eabb3"),
           text(74, 355, "Each box groups related Lean results.", 12, "#8eabb3"),
           text(54, 579, "Gamma input throughout this stage", 15, "#d2c6a9", 500),
           text(54, 601, "Sampling, contour bounds, and transform identities.", 12, "#9faab7"),
           text(700, 674, "TWO INPUTS TO COMPLETION", 10, "#a9b4c2", 600, "middle", 'letter-spacing="1"'),
           text(700, 699, "Q = 0 + restricted Fourier vanishing", 12.5, "#b8c1cd", 400, "middle"),
           text(54, 919, "KERNEL-CHECKED FOUNDATIONS", 10, "#a2d4b5", 600, extra='letter-spacing=".8"'),
           text(54, 942, "propext · Classical.choice · Quot.sound", 11.5, "#a9b4c2"),
           text(54, 963, "No sorrys or added axioms", 12, "#a9b4c2"),
           '<g class="edges" fill="none" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">'])
    node_by_id = {n["id"]: n for n in NODES}
    for a, b, path in EDGES:
        kind = "result" if b == "odd" else node_by_id[a]["kind"]
        if kind == "bridge":
            kind = "gamma"
        color = COLORS[kind][1]
        out.append(f'<path class="edge" data-from="{a}" data-to="{b}" d="{path}" stroke="{color}" marker-end="url(#arrow-{kind})"/>')
    out.append('</g>')
    out.append(text(932, 311, "contour tools", 10, "#829aa3", 400, "middle"))
    for n in NODES:
        out.append(node_svg(n))
    out.extend([text(54, 1030, "Grouped proof stages; selected dependency arrows.", 10.5, "#99a5b4"),
                text(1346, 1030, "EG equations proved. Categorical reconstruction is outside this formalization.", 10.5, "#99a5b4", anchor="end"),
                '</g></svg>'])
    return '\n'.join(out)


HTML = '''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>The complete odd-order proof · Haagerup–Izumi · __THEME__ theme</title>
<style>
:root{color-scheme:__THEME__}
*{box-sizing:border-box}body{margin:0;background:#101318;color:#e8e5df;font:15px "Adwaita Sans",system-ui,sans-serif}
main{max-width:1448px;margin:24px auto;padding:0 24px}nav{display:flex;align-items:center;gap:9px;margin:0 0 14px;flex-wrap:wrap}
.hint{margin-right:auto;color:#a9b4c2;font-size:13px}button,.download{font:inherit;font-size:12px;color:#c9d3df;background:#1c2026;border:1px solid #39424e;padding:9px 13px;border-radius:8px;text-decoration:none;cursor:pointer}
button:hover,.download:hover{background:#2a323b}button:focus-visible,a:focus-visible{outline:3px solid #68bfd2;outline-offset:3px}
.canvas{background:#14171c;border:1px solid #303640;border-radius:5px;overflow:hidden;box-shadow:0 8px 36px #31432908}.canvas>svg{display:block;width:100%;height:auto}
.node{cursor:pointer;outline:none}.node .card{transition:stroke-width .12s}.node:hover .card,.node:focus-visible .card{stroke-width:2.5}
.canvas.tracing .node,.canvas.tracing .edge{opacity:.22}.canvas.tracing .node.in-trace,.canvas.tracing .edge.in-trace{opacity:1}.node.selected .card{stroke-width:3}
.edge.in-trace{stroke-width:2.3}aside{background:#14171c;border:1px solid #303640;border-radius:5px;padding:20px 24px;margin:16px 0 24px;display:grid;grid-template-columns:1fr 1fr;gap:18px 40px;min-height:135px}
aside h2{font-size:19px;margin:0 0 7px}aside p{line-height:1.55;color:#a9b4c2;margin:0}#sources{display:flex;flex-direction:column;gap:8px;overflow-wrap:anywhere}#sources a{color:#80cbdc;text-underline-offset:3px;font-size:13px}#sources small{color:#939faf;display:block;margin-top:2px}#status{font-size:11px;letter-spacing:.08em;text-transform:uppercase;color:#a9b4c2;margin-bottom:7px}
@media(max-width:700px){main{padding:0 10px;margin:12px auto}.canvas{overflow:auto}.canvas>svg{min-width:1000px}aside{grid-template-columns:1fr;padding:16px}.hint{flex-basis:100%;margin-bottom:5px}}
@media print{body{background:#14171c;print-color-adjust:exact;-webkit-print-color-adjust:exact}main{max-width:none;margin:0;padding:0}nav,aside{display:none}.canvas{border:0;box-shadow:none;border-radius:0}.canvas.tracing .node,.canvas.tracing .edge{opacity:1}.canvas>svg{width:100%;min-width:0}@page{size:landscape;margin:8mm}}
</style>
<main><nav aria-label="Flowchart tools"><span class="hint">Select a box to trace its prerequisites and inspect the Lean sources.</span><a class="download" href="__OTHER_STEM__.html">__OTHER_THEME__ theme</a><button id="reset">Reset view</button><a class="download" href="__STEM__.svg" download>SVG</a><a class="download" href="__STEM__.pdf" download>PDF</a><button id="print">Print</button></nav>
<div class="canvas" id="canvas">__SVG__</div>
<aside aria-live="polite"><div><div id="status">Complete formalization</div><h2 id="detail-title">Every odd natural number</h2><p id="detail">The explicit hyperbolic gamma construction supplies the full analytic interface. The resulting complex coefficient data satisfy all Evans–Gannon equations.</p></div><div id="sources"></div></aside></main>
<script>
const nodes=__NODES__,edges=__EDGES__,byId=new Map(nodes.map(n=>[n.id,n]));
const canvas=document.querySelector('#canvas'),sourceList=document.querySelector('#sources');
function ancestors(id){const found=new Set([id]),todo=[id];while(todo.length){const v=todo.pop();for(const [a,b] of edges)if(b===v&&!found.has(a)){found.add(a);todo.push(a)}}return found}
function sources(n){sourceList.replaceChildren();for(const s of n.sources){const a=document.createElement('a');a.href='../HaagerupIzumi/'+s.file;a.target='_blank';a.rel='noopener';a.textContent=s.theorem;const small=document.createElement('small');small.textContent=s.file+' · line '+s.line;const item=document.createElement('div');item.append(a,small);sourceList.append(item)}}
function select(id){const n=byId.get(id),set=ancestors(id);canvas.classList.add('tracing');document.querySelectorAll('.node').forEach(el=>{const active=el.dataset.node===id;el.classList.toggle('in-trace',set.has(el.dataset.node));el.classList.toggle('selected',active);el.setAttribute('aria-pressed',String(active))});document.querySelectorAll('.edge').forEach(el=>el.classList.toggle('in-trace',set.has(el.dataset.from)&&set.has(el.dataset.to)));document.querySelector('#status').textContent='Selected stage · '+(set.size-1)+' prerequisite stages';document.querySelector('#detail-title').textContent=n.title;document.querySelector('#detail').textContent=n.detail;sources(n)}
function reset(){canvas.classList.remove('tracing');document.querySelectorAll('.node').forEach(el=>{el.classList.remove('selected','in-trace');el.setAttribute('aria-pressed','false')});document.querySelectorAll('.edge').forEach(el=>el.classList.remove('in-trace'));document.querySelector('#status').textContent='Complete formalization';document.querySelector('#detail-title').textContent='Every odd natural number';document.querySelector('#detail').textContent='The explicit hyperbolic gamma construction supplies the full analytic interface. The resulting complex coefficient data satisfy all Evans–Gannon equations.';sources(byId.get('odd'))}
document.querySelectorAll('.node').forEach(el=>{el.addEventListener('click',()=>select(el.dataset.node));el.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();select(el.dataset.node)}})});document.querySelector('#reset').addEventListener('click',reset);document.querySelector('#print').addEventListener('click',()=>window.print());document.addEventListener('keydown',e=>{if(e.key==='Escape')reset()});reset();
</script></html>
'''


def main():
    dark_svg = build_svg()
    for theme in ("dark", "light"):
        stem = "formalization_flowchart" + ("_light" if theme == "light" else "")
        other_stem = "formalization_flowchart" + ("_light" if theme == "dark" else "")
        svg = light_palette(dark_svg) if theme == "light" else dark_svg
        template = light_palette(HTML) if theme == "light" else HTML
        html = template.replace("__SVG__", svg).replace(
            "__NODES__", json.dumps(NODES, ensure_ascii=False)).replace(
            "__EDGES__", json.dumps([(a, b) for a, b, _ in EDGES])).replace(
            "__THEME__", theme).replace("__STEM__", stem).replace(
            "__OTHER_STEM__", other_stem).replace(
            "__OTHER_THEME__", "Light" if theme == "dark" else "Dark")
        (OUT / f"{stem}.svg").write_text(svg, encoding="utf-8")
        (OUT / f"{stem}.html").write_text(html, encoding="utf-8")
    print(f"Built dark and light maps with {len(NODES)} proof stages and "
          f"{len(EDGES)} dependency arrows in {OUT}")


if __name__ == "__main__":
    main()
