import FiniteOrderMixing.Cited.Kolmogorov
import FiniteOrderMixing.Cited.Khintchine
import FiniteOrderMixing.Cited.GaussianMoment
import FiniteOrderMixing.Cited.GaussianLimit
import FiniteOrderMixing.Cited.HLWord
import FiniteOrderMixing.Cited.HLProcess
import FiniteOrderMixing.Cited.HLColouring

/-!
# Results cited by the paper

The paper quotes the following results from the literature.  They are all proved in Lean in the
folder `FiniteOrderMixing/Cited`, so the formalisation uses no axioms beyond Lean's standard ones.

* `Cited/Kolmogorov.lean` — Kolmogorov extension for a finite alphabet [Kallenberg, Thm 8.23].
* `Cited/Khintchine.lean` — Khintchine's inequality with the Gaussian constant [Haagerup].
* `Cited/GaussianMoment.lean` — the even moments `E G^{2p} = (2p-1)!!` of a standard Gaussian.
* `Cited/GaussianLimit.lean` — moments of a Gaussian weak limit [Billingsley, Thm 3.4–3.5].
* `Cited/HLWord.lean`, `Cited/HLProcess.lean`, `Cited/HLColouring.lean` — the finitely dependent
  colourings of Holroyd and Liggett, in the form the construction needs: for every `m ≥ 1` a
  stationary, `2m`-dependent colouring with at least four colours, proper at range `m`.
-/
