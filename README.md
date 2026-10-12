# Finite-order mixing without the CLT — Lean formalization

Each main theorem file contains its statement and proof, in sections named `Statement` and `Proof`.
The declarations below belong to the namespace `FiniteOrderMixing`:

| Paper | Main file | Statement | Proof |
| --- | --- | --- | --- |
| Theorem A | `FiniteOrderMixing/TheoremA.lean` | `TheoremA` | `theoremA` |
| Theorem B | `FiniteOrderMixing/TheoremB.lean` | `TheoremB` | `theoremB` |
| Theorem C | `FiniteOrderMixing/TheoremC.lean` | `TheoremC` | `theoremC` |

The supporting modules contain the constructions and shared vocabulary. Symbolic properties
are in `Statements.lean`, and the stationary hierarchy law is constructed in `HierarchyLaw.lean`.
The torus and physical-realisation helpers are in `Realisation/Torus.lean` and
`Realisation/Physical.lean`. Auxiliary inputs from the literature are in `Cited/`.
These paths are relative to `FiniteOrderMixing/`.

## Verification

Install Git and Lean's elan toolchain manager:
https://github.com/leanprover/elan#installation

Clone this repository. From the repository root, run:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

Keep lean-toolchain and lake-manifest.json: these pin Lean and dependency
versions. Do not run lake update unless intentionally upgrading dependencies.
Internet access is required for the initial downloads. The .lake directory is
not tracked by this repository; downloaded dependencies and build files can occupy
several GB locally.

The axiom check should print:

```text
'FiniteOrderMixing.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.plane_wandering_deriv_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.catMap_sq_analyticAnosov' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.catCod_uniformlyHyperbolic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.theoremB_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteOrderMixing.theoremB_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms. Holroyd–Liggett, the required Khintchine
inequality, finite-alphabet Kolmogorov extension, and the Gaussian moment
results have proofs in this package. There are no project axioms.

The result covers Theorem C, including exclusion of centered Gaussian
subsequential limits N(0,v) for every v >= 0.

## Theorems A and B

The main dynamical statement and proof files are `TheoremA.lean` and `TheoremB.lean` in
`FiniteOrderMixing/`; their supporting files are in `FiniteOrderMixing/Realisation/`. Theorem A is
`FiniteOrderMixing.theoremA : TheoremA`, with both declarations in `TheoremA.lean`.
Theorem B is `FiniteOrderMixing.theoremB : TheoremB` (`TheoremB.lean`),
with a `C^∞` diffeomorphism as in the paper. The earlier auxiliary variant
`FiniteOrderMixing.theoremB_lipschitz` (`Realisation/Surface.lean`) is stated for Lipschitz observables
and a chart-Lipschitz metric.

Theorem A is proved without axioms beyond Lean's standard ones. Lemma 3.9 is
replaced by an explicit arithmetic coding of a two-symbol horseshoe for A^2
(`Realisation/CatHorseshoe.lean`). The trigonometric approximation in (v) uses
polynomials composed with a trigonometric polynomial (`Realisation/Torus.lean`).
The statement also includes a real-analytic Anosov certificate for the ambient map
and uniform hyperbolicity of the coded horseshoe. `Realisation/TorusGeometry.lean`
defines the torus-specific certificate using actual open quotient charts and the
standard tangent trivialization. `Realisation/CatAnosov.lean` proves it for A^2:
the constant stable and unstable lines span the tangent space, and the forward
stable and backward unstable derivatives contract by `(7 - 3√5)/2` at each step.
Theorem B is proved with `C^∞` regularity, without additional axioms.
`TheoremB` states the smooth conclusion directly, and `theoremB` proves it.
For each `R ≥ 2`, it gives
one smooth diffeomorphism with all six conclusions, including a uniformly hyperbolic
horseshoe and a nonempty open set in the statistical basin of its physical measure.
The orbit-following conclusion needed from strong pluripotency
(Kiriki–Li–Nakano–Soma–Vargas) is proved by an explicit construction. The general theorem,
including arbitrarily small perturbations near a given map, is not formalised here:

* `Realisation/PlaneDiffeo.lean`, `PlaneModel.lean`: a `C^∞` diffeomorphism `T₀` of
  the plane, equal to the identity outside `(-5, 5)²`, which is the affine
  middle-thirds horseshoe `(x, y) ↦ (3x - 2[b], (y + 2[b])/3)` on two vertical strips
  and maps the middle (gap) strip by `(x, y) ↦ (1 - y, 1/2 + γ(x - 1/2))`, turning the
  unstable direction into the stable one. `T₀` is a composition of fibrewise
  contractions, their inverses and a twist map.
* `Realisation/PlanePerturb.lean`: infinitely many bump translations by `e_k` on
  balls of radius `ρ_k`, `C^r` as soon as `Σ |e_k| ρ_k^{-r} < ∞`.
* `Realisation/Itinerary.lean`, `WanderBox.lean`, `WanderOrbit.lean`,
  `WanderAverage.lean`: a box whose orbit follows the symbols of a given `ω` in blocks
  of linearly growing length. Each block starts with a head of `O(√k + log k)` symbols that
  repeat the flipped, reversed tail of the previous block; this makes each return
  through the gap strip accurate to within `3^{-head}`, and the remaining error is
  absorbed by the `k`-th bump. Box sizes decay geometrically, exits are polynomially
  separated, and heads have density zero, so time-averaged distances to the orbit of
  `ω` tend to `0` (`plane_wandering`).
* `Realisation/SmoothDecay.lean`, `SmoothWandering.lean`: the head includes
  `⌊√(k+2)⌋`, so `|e_k| ≤ 3^{-⌊√(k+2)⌋}`. Since `ρ_k^{-1} = 100(k+2)²`,
  `Σ |e_k| ρ_k^{-m}` is finite for every derivative order `m`. Only the first
  derivative needs a smallness bound for invertibility. This proves smoothness
  of the same map and its inverse, while the sublinear heads still have density zero
  (`plane_wandering_deriv_smooth`).
* `Realisation/Transplant.lean`: the planar model is conjugated into a chart of the
  surface by a small affine map and extended by the identity.

Everything else in Part I is proved, including Lemma 3.4, Proposition 3.5 (by a
quantitative moment argument instead of Prokhorov's theorem), Lemma 3.10 and
Proposition 3.12 (generic points come from a law of large numbers derived from
exponential mixing, not from Birkhoff's theorem).

In `theoremB`, `M` is any nonempty compact Hausdorff smooth surface without boundary
with a (continuous) Riemannian metric, including disconnected surfaces. Connectedness and a
globally finite intrinsic Riemannian distance are not assumed. The proof constructs the auxiliary
metric `d(x,y) = min(2, d_R(x,y))`, where the intrinsic extended distance `d_R` may be infinite
between components. This metric has the original topology and leaves the tangent norms and
the `C¹` norm unchanged (`Realisation/BoundedRiemann.lean`). The existing construction extends
the map by the identity outside one chart, so it works on disconnected surfaces as well.
`theoremB_metric` retains the previous version for a globally finite intrinsic distance
(Mathlib's `IsRiemannianManifold`). All statistical conclusions of the paper are retained, with `C^∞` regularity:

* `‖f‖_{C¹(M)} = ‖f‖_∞ + ‖Df‖_∞`, with the Riemannian norm on tangent spaces
  (`Realisation/RiemannC1.lean`). Item (ii) is the estimate
  `|μ(∏ fᵢ ∘ T^{nᵢ}) - ∏ μ(fᵢ)| ≤ C e^{-cΔ} ∏ ‖fᵢ‖_{C¹}` for all `fᵢ ∈ C¹(M)`, item (iv)
  is an open `C¹`-ball around `f₀`, and item (vi) excludes exponential mixing of order
  `2R + 2` in `C¹(M)`. For the auxiliary metric, a `C¹` bound is a Lipschitz bound: below
  distance `2` use the derivative estimate along paths, and at distance `2` use
  `|f x - f y| ≤ 2‖f‖_∞`. This also covers points in different components.
* The two-symbol horseshoe `Λ` is coded by the full shift and is uniformly hyperbolic
  for the Riemannian metric (`IsHyperbolicSet`, `Realisation/Hyperbolic.lean`,
  `TransplantHyp.lean`).
* `μ` is physical: `m(B_T(μ)) > 0` for every smooth volume `m`, i.e. every measure with
  a smooth positive density in charts (`Realisation/SmoothVolume.lean`).

The distance is shown to be locally bounded by the distance in charts
(`chartUpperLip_of_edist_le_riemannian`), which is the only metric property used by the
transplant. It applies both to the intrinsic finite metric and to the auxiliary bounded metric.

## Theorem C

Theorem C is the symbolic construction underlying Theorems A and B. Its statement is
`FiniteOrderMixing.TheoremC`, and its proof declaration is
`FiniteOrderMixing.theoremC : TheoremC`, both in
[`FiniteOrderMixing/TheoremC.lean`](FiniteOrderMixing/TheoremC.lean).
The conclusions are recorded in `SymbolicProperties R ν`
([`Statements.lean`](FiniteOrderMixing/Statements.lean)).

For every integer `R ≥ 2`, set `L = 2R + 2`. The theorem gives a full-support,
shift-invariant Borel probability measure `ν` on `Σ = {-1,1}^ℤ`.
Writing `Zᵢ(ω) = ωᵢ` and `Sₙ = ∑_{j=0}^{n-1} Zⱼ`, all five conclusions hold
for this same measure:

* **(i) Symmetric signs and tuplewise independence.** The stationary coordinate
  process has symmetric `{-1,1}` marginals, and any collection of at most
  `2R + 1` coordinates with distinct indices is jointly independent.
* **(ii) Independence of separated windows.** There is a finite constant `K_R`
  such that, for every `2 ≤ s ≤ R`, the coordinate vectors on `s` ordered,
  nonempty finite intervals are jointly independent whenever every successive
  distance exceeds `K_R` times the largest interval cardinality.
* **(iii) Finite-order exponential mixing.** For every `0 < θ < 1`, the shift
  is exponentially mixing of every order `2 ≤ s ≤ R` on the symbolic
  `d_θ`-Lipschitz class `F_θ(Σ)`, encoded by `HolderObs θ`. Varying `θ`
  covers the Hölder classes used in the paper.
* **(iv) Moment deficit and no Gaussian subsequential limit.** There are
  `δ > 0` and `n₀` such that
  `E_ν[(Sₙ/√n)^L] ≤ (L-1)!! - δ` for all `n ≥ n₀`.
  No subsequence of `Sₙ/√n` converges in distribution to `N(0,v)` for any
  `v ≥ 0`, including the degenerate law at `v = 0`.
* **(v) Failure of higher-order exponential mixing.** There are `c, C > 0`
  such that, for every sufficiently large integer `N`, some times
  `0 ≤ n₁ < ··· < n_L < N` have minimum successive gap at least `N/C` and satisfy
  `-E_ν[∏_{i=1}^L Z_{n_i}] ≥ c N^{-L/2}`.
  Consequently, exponential mixing of order `L = 2R + 2` fails on `F_θ(Σ)`
  for every `0 < θ < 1`. This does not assert failure of qualitative mixing
  at that order.

The proof first constructs the stationary nested-marker law using
`exists_hierarchyLaw` in [`HierarchyLaw.lean`](FiniteOrderMixing/HierarchyLaw.lean),
then applies `symbolic_of_hierarchyLaw` in
[`Symbolic.lean`](FiniteOrderMixing/Symbolic.lean). Thus the hierarchy law is
constructed, not assumed in the final statement.

The main supporting modules, with paths relative to `FiniteOrderMixing/`, are:

| Modules | Role in Theorem C |
| --- | --- |
| `Construction.lean`, `Stationarity.lean`, `Dependence.lean`, `HierarchyLaw.lean` | Nested markers, stationarity and finite-level dependence |
| `Bias.lean`, `BlockLaws.lean` | Recursive block laws and their negative `L`-point correlations |
| `Limit.lean`, `Properties.lean` | Limiting measure, full support, shift invariance and tuplewise independence |
| `Mixing.lean` | Separated-window independence and exponential mixing through order `R` |
| `Moment.lean` | Moment deficit, exclusion of Gaussian subsequential limits and the higher-order correlation bound |
| `Symbolic.lean` | Assembly of all five conclusions into `SymbolicProperties` |

The coloring proof establishes the sufficient 2m-dependent, range-m proper
version used by the construction. Some intermediate constants differ from
the manuscript without weakening Theorem C's existential conclusions.

Verification uses `lake build` and `lake env lean CheckAxioms.lean`. The eight checked
declarations use only the three standard axioms above. Run these checks again after cloning.
