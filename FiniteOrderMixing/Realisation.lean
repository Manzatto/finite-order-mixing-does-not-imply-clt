module
public import FiniteOrderMixing.Realisation.TorusGeometry
public import FiniteOrderMixing.Realisation.Defs
public import FiniteOrderMixing.Realisation.Transfer
public import FiniteOrderMixing.Realisation.Variance
public import FiniteOrderMixing.Realisation.Robust
public import FiniteOrderMixing.Realisation.Generic
public import FiniteOrderMixing.Realisation.CatHorseshoe
public import FiniteOrderMixing.Realisation.CatAnosov
public import FiniteOrderMixing.Realisation.Torus
public import FiniteOrderMixing.TheoremA
public import FiniteOrderMixing.Realisation.PlaneDiffeo
public import FiniteOrderMixing.Realisation.PlaneModel
public import FiniteOrderMixing.Realisation.PlaneDigits
public import FiniteOrderMixing.Realisation.PlanePerturb
public import FiniteOrderMixing.Realisation.Itinerary
public import FiniteOrderMixing.Realisation.WanderBox
public import FiniteOrderMixing.Realisation.WanderOrbit
public import FiniteOrderMixing.Realisation.WanderAverage
public import FiniteOrderMixing.Realisation.Transplant
public import FiniteOrderMixing.Realisation.Surface
public import FiniteOrderMixing.Realisation.RiemannC1
public import FiniteOrderMixing.Realisation.WanderDeriv
public import FiniteOrderMixing.Realisation.SmoothDecay
public import FiniteOrderMixing.Realisation.SmoothWandering
public import FiniteOrderMixing.Realisation.Hyperbolic
public import FiniteOrderMixing.Realisation.TransplantHyp
public import FiniteOrderMixing.Realisation.SmoothVolume
public import FiniteOrderMixing.Realisation.BoundedRiemann
public import FiniteOrderMixing.Realisation.Physical
public import FiniteOrderMixing.TheoremB

/-!
# Part I: dynamical realisations (Theorems A and B)

The main statements and proofs are in `TheoremA.lean` and `TheoremB.lean` in `FiniteOrderMixing/`;
the supporting files are in `FiniteOrderMixing/Realisation/`.

* `Realisation/Defs.lean` — shared coding and statistical definitions;
* `Realisation/Transfer.lean` — Lemma `lem:transfer`: transport of Theorem C through a coding;
* `Realisation/Variance.lean` — Lemma `lem:variance` and a law of large numbers;
* `Realisation/Robust.lean` — Proposition `prop:robustness`;
* `Realisation/Generic.lean` — generic points of `ν` (used in Proposition `prop:physical-transfer`);
* `Realisation/CatHorseshoe.lean` — Lemma `lem:fixed-horseshoe`: an explicit horseshoe for `A²`;
* `Realisation/TorusGeometry.lean`, `CatAnosov.lean` — quotient-chart analyticity and the
  constant stable/unstable splitting with uniform derivative contraction for `A²`;
* `Realisation/Torus.lean` — smooth observables, trigonometric approximation, and cat-map continuity;
* `TheoremA.lean` — `TheoremA` and `theoremA`, **Theorem `thm:analytic`**;
* `Realisation/PlaneDiffeo.lean` — diffeomorphisms of the plane: inverse function theorem,
  fibrewise maps, twists, contractions;
* `Realisation/PlaneModel.lean` — the planar horseshoe model `T₀` with a gap map turning the
  unstable direction into the stable one;
* `Realisation/PlaneDigits.lean` — ternary digits and the coding of the middle-thirds horseshoe;
* `Realisation/PlanePerturb.lean` — infinitely many `C^r`-small bump translations;
* `Realisation/Itinerary.lean`, `WanderBox.lean`, `WanderOrbit.lean`, `WanderAverage.lean` — the
  wandering box following a prescribed orbit: `plane_wandering`;
* `Realisation/Transplant.lean` — transplant into a chart of the surface: `surface_wandering`
  (strong pluripotency, Theorem `thm:physical-pluripotency-input`, in the form used);
* `Realisation/Surface.lean` — `theoremB_lipschitz`, **Theorem `thm:physical`** for Lipschitz observables
  and a chart-Lipschitz metric;
* `Realisation/RiemannC1.lean` — the `C¹` norm `‖f‖_∞ + ‖Df‖_∞` of a Riemannian metric, and
  `Lip(f) ≤ ‖Df‖_∞` for the Riemannian distance;
* `Realisation/WanderDeriv.lean`, `Hyperbolic.lean`, `TransplantHyp.lean` — uniform hyperbolicity
  of the horseshoe, and the chart estimate for a Riemannian distance;
* `Realisation/SmoothDecay.lean`, `SmoothWandering.lean` — square-root heads and summability
  in every derivative order, giving a single `C^∞` wandering diffeomorphism;
* `Realisation/SmoothVolume.lean` — smooth volumes charge open sets;
* `Realisation/BoundedRiemann.lean` — a compatible bounded metric and the `C¹` estimate on
  possibly disconnected Riemannian manifolds;
* `Realisation/Physical.lean` — `PhysicalRealisation` and the metric-based auxiliary theorems;
* `TheoremB.lean` — `TheoremB` and `theoremB`, **Theorem `thm:physical`**, with `C^∞` regularity,
  including disconnected surfaces.
-/
