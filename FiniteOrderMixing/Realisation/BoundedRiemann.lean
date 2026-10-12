import FiniteOrderMixing.Realisation.RiemannC1

/-!
# An auxiliary metric on a possibly disconnected Riemannian manifold

The intrinsic Riemannian distance may be infinite between components. Truncating it at `2`
gives a finite metric with the original topology. A `C¹` bound is still a Lipschitz bound:
use the path estimate at distances less than `2`, and twice the supremum bound otherwise.
The Riemannian norms on tangent spaces are unchanged.
-/

open Set Filter Topology Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff

namespace FiniteOrderMixing

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] [T3Space M]

/-- The intrinsic Riemannian distance truncated at `2`, with the original topology. -/
@[instance_reducible] noncomputable def boundedRiemannianMetric : MetricSpace M := by
  let d : M → M → ℝ≥0∞ := fun x y => min 2 (riemannianEDist I x y)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofEDistOfTopology d
    (fun x => by simp [d, riemannianEDist_self])
    (fun x y => by simp only [d, riemannianEDist_comm (I := I) (x := x) (y := y)])
    (fun x y z => by
      dsimp [d]
      grw [riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z),
        min_add_distrib, min_le_right])
    (fun x => (basis_sets (𝓝 x)).to_hasBasis'
      (fun s hs => by
        obtain ⟨c, hc, hcs⟩ := setOfPred_riemannianEDist_lt_subset_nhds' I hs
        refine ⟨min c 1, by positivity, fun y hy => hcs ?_⟩
        change min 2 (riemannianEDist I x y) < min c 1 at hy
        have hlt : riemannianEDist I x y < min c 1 := by
          rcases (min_lt_iff.1 hy) with h | h
          · exact False.elim (by have := h.trans_le (min_le_right c 1); norm_num at this)
          · exact h
        exact hlt.trans_le (min_le_left _ _))
      (fun c hc => by
        filter_upwards [eventually_riemannianEDist_lt I x hc] with y hy
        exact (min_le_right _ _).trans_lt hy))
  letI : EMetricSpace M := EMetricSpace.ofT0PseudoEMetricSpace M
  exact EMetricSpace.toMetricSpace fun x y =>
    ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (min_le_left _ _)

/-- The auxiliary metric has extended distance `min 2 d_R`. -/
lemma boundedRiemannianMetric_edist (x y : M) :
    letI := boundedRiemannianMetric I M
    edist x y = min 2 (riemannianEDist I x y) := rfl

end Metric

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- A `C¹` bound controls the auxiliary metric even across different components. -/
lemma C1BoundM.lipBound_of_boundedRiemannian
    (hd : ∀ x y : M, edist x y = min 2 (riemannianEDist I x y))
    {f : M → ℝ} {A : ℝ} (h : C1BoundM I f A) : LipBound f A := by
  obtain ⟨hf, a, b, ha, hb, hab⟩ := h
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have hb0 : 0 ≤ b := (ContinuousLinearMap.opNorm_nonneg _).trans (hb x)
    exact (ha x).trans (by linarith)
  · have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha x)
    have hb0 : 0 ≤ b := (ContinuousLinearMap.opNorm_nonneg _).trans (hb x)
    have hA0 : 0 ≤ A := by linarith
    by_cases hsmall : dist y x < 2
    · have hdy : edist y x < 2 := by
        rw [edist_dist]
        simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2)).2 hsmall
      have heq : riemannianEDist I y x = edist y x := by
        rw [hd] at hdy ⊢
        exact (min_eq_right (le_of_lt ((min_lt_iff.1 hdy).resolve_left (lt_irrefl _)))).symm
      have hbound : |f x - f y| ≤ b * dist x y := by
        apply le_of_forall_pos_lt_add
        intro ε hε
        set δ : ℝ := ε / (b + 1)
        have hδ : 0 < δ := by positivity
        have hlt : riemannianEDist I y x < edist y x + ENNReal.ofReal δ := by
          rw [heq]
          exact ENNReal.lt_add_right (edist_ne_top y x) (by simpa using hδ)
        obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
        have key := ofReal_abs_sub_le_pathELength hf hb hγ
        rw [hγ0, hγ1] at key
        have h2 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (b * (dist x y + δ)) := by
          refine key.trans ?_
          rw [ENNReal.ofReal_mul hb0]
          gcongr
          refine hlen.le.trans ?_
          rw [edist_dist, dist_comm, ← ENNReal.ofReal_add dist_nonneg hδ.le]
        have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
        calc |f x - f y| ≤ b * (dist x y + δ) := h3
          _ = b * dist x y + b * δ := by ring
          _ < b * dist x y + ε := by
            have : b * δ < ε := by
              simp only [δ]
              rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
              nlinarith
            linarith
      exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
    · have hlarge : 2 ≤ dist x y := by simpa [dist_comm] using le_of_not_gt hsmall
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ 2 * a := by linarith [ha x, ha y]
        _ ≤ A * dist x y := by nlinarith

end Bounds

end FiniteOrderMixing
