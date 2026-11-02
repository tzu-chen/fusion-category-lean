# Documentation of the odd-order formalization

Everything here concerns the main theorem `HaagerupIzumi.exists_EGEquations_odd`:
its complete declaration dependency graph, a smaller proof flowchart, and
experiments that remove one hypothesis at a time.

## Declaration dependency graph

The [complete declaration dependency graph](exists_EGEquations_odd_dependencies.html)
starts at project declarations with only library dependencies and ends at
`HaagerupIzumi.exists_EGEquations_odd`. It includes the explicit gamma construction,
all project prerequisites, private helpers, and generated declarations. Search,
pan, zoom, inspect Lean source, and select nodes to list their dependencies.
[SVG](exists_EGEquations_odd_dependencies.svg),
[DOT](exists_EGEquations_odd_dependencies.dot), and
[JSON](exists_EGEquations_odd_dependencies.json) contain the full graph.

Arrows point **from a dependency to its user**. Dashed arrows mean the dependency
occurs in the user's statement; solid arrows mean it occurs only in its proof or
definition body. Every direct project arrow is retained, including arrows also
implied by longer paths. There is no depth limit, node cap, contraction, or
transitive reduction. External Mathlib/Lean references are listed for each node,
but those libraries' internal graphs are not expanded. The JSON records the
source hashes, tool provenance, exact counts, and Lean's axiom audit.
Lean can regenerate the same equation or congruence theorem in multiple modules;
these names are merged only after checking that their direct dependencies and
declaration metadata agree. Their generating modules are retained in the JSON.

The endpoint assumes only `Odd n`. Unlike `Concrete.EGEquations_concrete`, it
does not take the hyperbolic-gamma interface as a premise. Its axiom audit is
`[propext, Classical.choice, Quot.sound]`.

These files were generated from the modules in this archive; the JSON's
`provenance.source_sha256` records the hash of each of the 113 modules with
declarations in the graph. Extraction used a locally adapted copy of [result-graph](https://github.com/PierreSenellart/result-graph)
(Apache-2.0). The generator is not included because it requires a machine-specific
resource guard; it is in `lean/docs/` and `lean/tools/dependency_graph/` of
<https://github.com/tzu-chen/haagerup/tree/b4b618f/lean>.

The SVG preserves the entire vector graph while using a bounded default viewport;
use the HTML for interactive exploration.

## Proof flowchart

The smaller [interactive proof map](formalization_flowchart.html) traces the completed
odd-order Evans–Gannon formalization. Select a stage to highlight its prerequisites
and open the corresponding Lean declarations. SVG, PDF, and PNG versions are
provided for sharing.

The diagram is available in [dark](formalization_flowchart.html) and
[light](formalization_flowchart_light.html) themes, with matching SVG, PDF, and
PNG exports. Both use uppercase labels and monospace theorem names.
Cyan denotes gamma results, amber denotes finite Fourier analysis, green denotes
algebraic completion, and magenta denotes the final theorem.

Boxes group related results, and arrows show selected mathematical dependencies.
For example, Product transforms includes the left-product, right-product, and
negative-column calculations and their contour prerequisites. Shared inputs and
some transitive arrows are omitted: the gamma interface supplies analytic input
throughout the Fourier stage. This is an overview, not an exhaustive dependency
or file-import graph. The conclusion concerns the Evans–Gannon equations, with
categorical reconstruction outside this formalization.

Regenerate from the project root (Python uses only the standard library;
exports require `rsvg-convert`):

```sh
python docs/build_formalization_flowchart.py
rsvg-convert -w 2100 -o docs/formalization_flowchart.png docs/formalization_flowchart.svg
rsvg-convert -f pdf -o docs/formalization_flowchart.pdf docs/formalization_flowchart.svg
rsvg-convert -w 2100 -o docs/formalization_flowchart_light.png docs/formalization_flowchart_light.svg
rsvg-convert -f pdf -o docs/formalization_flowchart_light.pdf docs/formalization_flowchart_light.svg
```

Edit the generator, rather than the generated HTML or SVG.

## Ablation experiments

The files in `ablation/` remove one hypothesis at a time. They are standalone
and outside the default build target; after `lake build`, check one from the
project root with `lake env lean docs/ablation/FILE.lean`.

The [later range ablation study](ablation/later_range_ablation.md) removes one
inequality at a time from the Section 6 product-transform residue formulas. It
gives exact nonzero errors using the original gamma function, standalone Lean
certificates ([left](ablation/LeftProductRangeAblation.lean),
[right](ablation/RightProductRangeAblation.lean)), and
[dependency paths](ablation/later_range_ablation_paths.json) to the final theorem.
The study distinguishes a false weakened intermediate formula from downstream
theorems whose existing proofs use that formula.

The [no-pinch ablation](ablation/gamma_contour_ablation.md) removes the first
clause of `K4NoPinch`, after which two admissible corrected contours differ by
exactly −1/2. That integral discrepancy is a mathematical derivation.
[Its Lean file](ablation/GammaContourAblation.lean) certifies only the geometry
and finite-sum accounting. The study also records
[dependency paths](ablation/gamma_contour_ablation_paths.json).

[`AssumptionAblationPilot.lean`](ablation/AssumptionAblationPilot.lean) holds
small local logical tests, which are not counterexamples to Evans–Gannon.
