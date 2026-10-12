import FiniteOrderMixing.Realisation.TorusGeometry
import FiniteOrderMixing.Realisation.Defs
import FiniteOrderMixing.Realisation.Transfer
import FiniteOrderMixing.Realisation.Variance
import FiniteOrderMixing.Realisation.Robust
import FiniteOrderMixing.Realisation.Generic
import FiniteOrderMixing.Realisation.CatHorseshoe
import FiniteOrderMixing.Realisation.CatAnosov
import FiniteOrderMixing.Realisation.Torus
import FiniteOrderMixing.TheoremA
import FiniteOrderMixing.Realisation.PlaneDiffeo
import FiniteOrderMixing.Realisation.PlaneModel
import FiniteOrderMixing.Realisation.PlaneDigits
import FiniteOrderMixing.Realisation.PlanePerturb
import FiniteOrderMixing.Realisation.Itinerary
import FiniteOrderMixing.Realisation.WanderBox
import FiniteOrderMixing.Realisation.WanderOrbit
import FiniteOrderMixing.Realisation.WanderAverage
import FiniteOrderMixing.Realisation.Transplant
import FiniteOrderMixing.Realisation.Surface
import FiniteOrderMixing.Realisation.RiemannC1
import FiniteOrderMixing.Realisation.WanderDeriv
import FiniteOrderMixing.Realisation.SmoothDecay
import FiniteOrderMixing.Realisation.SmoothWandering
import FiniteOrderMixing.Realisation.Hyperbolic
import FiniteOrderMixing.Realisation.TransplantHyp
import FiniteOrderMixing.Realisation.SmoothVolume
import FiniteOrderMixing.Realisation.BoundedRiemann
import FiniteOrderMixing.Realisation.Physical
import FiniteOrderMixing.TheoremB

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
