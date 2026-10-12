import FiniteOrderMixing.Realisation.WanderDeriv
import FiniteOrderMixing.Realisation.RiemannC1

/-!
# Uniformly hyperbolic sets

`IsHyperbolicSet I T Λ`: `Λ` is a compact `T`-invariant set with a `DT`-invariant splitting
`T_x M = E^s_x ⊕ E^u_x` over `Λ` such that, for the Riemannian norms,
`‖D_x T^n v‖ ≤ C ρ^n ‖v‖` on `E^s_x` and `‖v‖ ≤ C ρ^n ‖D_x T^n v‖` on `E^u_x`.

`isHyperbolicSet_of_diag` is a criterion: if, through tangent isomorphisms `A_x : ℝ² → T_x M`
uniformly bounded with their inverses, the derivative cocycle of `T` is `diag(3^n, 3^{-n})`, then
`Λ` is uniformly hyperbolic.
-/

open Set Filter Topology Manifold Bundle

namespace FiniteOrderMixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- `Λ` is a **uniformly hyperbolic set** of the map `T`. -/
def IsHyperbolicSet (T : M → M) (Λ : Set M) : Prop :=
  IsCompact Λ ∧ T '' Λ = Λ ∧ ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
    ∃ Es Eu : ∀ x : M, Submodule ℝ (TangentSpace I x),
      (∀ x ∈ Λ, IsCompl (Es x) (Eu x)) ∧
      (∀ x ∈ Λ, (Es x).map (mfderiv I I T x : TangentSpace I x →ₗ[ℝ] TangentSpace I (T x)) =
        Es (T x)) ∧
      (∀ x ∈ Λ, (Eu x).map (mfderiv I I T x : TangentSpace I x →ₗ[ℝ] TangentSpace I (T x)) =
        Eu (T x)) ∧
      (∀ x ∈ Λ, ∀ n : ℕ, ∀ v ∈ Es x, ‖mfderiv I I (T^[n]) x v‖ ≤ C * ρ ^ n * ‖v‖) ∧
      (∀ x ∈ Λ, ∀ n : ℕ, ∀ v ∈ Eu x, ‖v‖ ≤ C * ρ ^ n * ‖mfderiv I I (T^[n]) x v‖)

lemma norm_snd_prod (s : ℝ) : ‖((0 : ℝ), s)‖ = |s| := by
  simp [Prod.norm_def]

lemma norm_fst_prod (t : ℝ) : ‖(t, (0 : ℝ))‖ = |t| := by
  simp [Prod.norm_def]

variable {I}

/-- **A criterion for uniform hyperbolicity.** -/
lemma isHyperbolicSet_of_diag {T : M → M} {Λ : Set M} (hΛ : IsCompact Λ) (hT : T '' Λ = Λ)
    (A : ∀ x : M, P2 →L[ℝ] TangentSpace I x) (B : ∀ x : M, TangentSpace I x →L[ℝ] P2)
    (hBA : ∀ x ∈ Λ, ∀ w, B x (A x w) = w) (hAB : ∀ x ∈ Λ, ∀ v, A x (B x v) = v)
    {K : ℝ} (hK : 0 < K) (hA : ∀ x ∈ Λ, ∀ w, ‖A x w‖ ≤ K * ‖w‖)
    (hB : ∀ x ∈ Λ, ∀ v, ‖B x v‖ ≤ K * ‖v‖)
    (hD : ∀ x ∈ Λ, ∀ (n : ℕ) w, mfderiv I I (T^[n]) x (A x w) = A (T^[n] x) ((diagL ^ n) w)) :
    IsHyperbolicSet I T Λ := by
  have hmaps : ∀ x ∈ Λ, T x ∈ Λ := fun x hx => hT ▸ mem_image_of_mem T hx
  have hit : ∀ x ∈ Λ, ∀ n : ℕ, T^[n] x ∈ Λ := fun x hx n => by
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  set Es : ∀ x : M, Submodule ℝ (TangentSpace I x) := fun x =>
    (Submodule.span ℝ {((0 : ℝ), (1 : ℝ))}).map (A x : P2 →ₗ[ℝ] TangentSpace I x)
  set Eu : ∀ x : M, Submodule ℝ (TangentSpace I x) := fun x =>
    (Submodule.span ℝ {((1 : ℝ), (0 : ℝ))}).map (A x : P2 →ₗ[ℝ] TangentSpace I x)
  have hEs : ∀ x (v : TangentSpace I x), v ∈ Es x ↔ ∃ s : ℝ, A x (0, s) = v := fun x v => by
    simp only [Es, Submodule.mem_map, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨s, by simp⟩
    · rintro ⟨s, rfl⟩; exact ⟨_, ⟨s, rfl⟩, by simp⟩
  have hEu : ∀ x (v : TangentSpace I x), v ∈ Eu x ↔ ∃ t : ℝ, A x (t, 0) = v := fun x v => by
    simp only [Eu, Submodule.mem_map, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨t, by simp⟩
    · rintro ⟨t, rfl⟩; exact ⟨_, ⟨t, rfl⟩, by simp⟩
  have hD1 : ∀ x ∈ Λ, ∀ w, mfderiv I I T x (A x w) = A (T x) (diagL w) := fun x hx w => by
    have h := hD x hx 1 w
    rw [pow_one] at h
    exact h
  refine ⟨hΛ, hT, K * K, 1 / 3, by positivity, by norm_num, by norm_num, Es, Eu, ?_, ?_, ?_, ?_, ?_⟩
  · -- complementarity
    intro x hx
    constructor
    · rw [Submodule.disjoint_def]
      intro v h1 h2
      obtain ⟨s, rfl⟩ := (hEs x v).1 h1
      obtain ⟨t, ht⟩ := (hEu x _).1 h2
      have := congrArg (B x) ht
      rw [hBA x hx, hBA x hx] at this
      simp only [Prod.mk.injEq] at this
      rw [← this.2]
      exact (A x).map_zero
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v = A x (0, (B x v).2) + A x ((B x v).1, 0) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, hAB x hx]
      rw [hv]
      exact Submodule.add_mem_sup ((hEs x _).2 ⟨_, rfl⟩) ((hEu x _).2 ⟨_, rfl⟩)
  · -- invariance of `E^s`
    intro x hx
    ext v
    simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe]
    rw [hEs]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨s, rfl⟩ := (hEs x u).1 hu
      exact ⟨3⁻¹ * s, by rw [hD1 x hx, diagL_apply]; simp⟩
    · rintro ⟨s, rfl⟩
      refine ⟨A x (0, 3 * s), (hEs x _).2 ⟨_, rfl⟩, ?_⟩
      rw [hD1 x hx, diagL_apply]; congr 1; ext <;> simp
  · -- invariance of `E^u`
    intro x hx
    ext v
    simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe]
    rw [hEu]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨t, rfl⟩ := (hEu x u).1 hu
      exact ⟨3 * t, by rw [hD1 x hx, diagL_apply]; simp⟩
    · rintro ⟨t, rfl⟩
      refine ⟨A x (3⁻¹ * t, 0), (hEu x _).2 ⟨_, rfl⟩, ?_⟩
      rw [hD1 x hx, diagL_apply]; congr 1; ext <;> simp
  · -- contraction on `E^s`
    intro x hx n v hv
    obtain ⟨s, rfl⟩ := (hEs x v).1 hv
    rw [hD x hx n, diagL_pow_apply]
    have h1 := hA _ (hit x hx n) ((3 : ℝ) ^ n * 0, s / 3 ^ n)
    have h2 := hB x hx (A x (0, s))
    rw [hBA x hx, norm_snd_prod] at h2
    rw [mul_zero, norm_snd_prod, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)] at h1
    calc ‖A (T^[n] x) (3 ^ n * 0, s / 3 ^ n)‖ ≤ K * (|s| / 3 ^ n) := by simpa using h1
      _ ≤ K * (K * ‖A x (0, s)‖ / 3 ^ n) := by gcongr
      _ = K * K * (1 / 3) ^ n * ‖A x (0, s)‖ := by rw [one_div_pow]; ring
  · -- expansion on `E^u`
    intro x hx n v hv
    obtain ⟨t, rfl⟩ := (hEu x v).1 hv
    rw [hD x hx n, diagL_pow_apply, zero_div]
    have h1 := hA x hx (t, 0)
    have h2 := hB _ (hit x hx n) (A (T^[n] x) (3 ^ n * t, 0))
    rw [hBA _ (hit x hx n), norm_fst_prod, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)] at h2
    rw [norm_fst_prod] at h1
    have h3 : |t| ≤ K * ‖A (T^[n] x) (3 ^ n * t, 0)‖ / 3 ^ n := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc ‖A x (t, 0)‖ ≤ K * |t| := h1
      _ ≤ K * (K * ‖A (T^[n] x) (3 ^ n * t, 0)‖ / 3 ^ n) := by gcongr
      _ = K * K * (1 / 3) ^ n * ‖A (T^[n] x) (3 ^ n * t, 0)‖ := by
          rw [one_div_pow]; ring

end FiniteOrderMixing
