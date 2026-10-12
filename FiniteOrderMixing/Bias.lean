import FiniteOrderMixing.Cited

/-!
# The finite-dimensional biasing lemma (Lemma `lem:bias`)

A *law* on the coordinates of a finite set `B` is a density `ρ ≥ 0` with respect to the uniform
average, depending only on the coordinates in `B`, with `avg B ρ = 1`.  Expectations are
`E_ρ[F] = avg B (ρ · F)`.

Main result: `exists_bias`.  If `ρ` is invariant under the global sign reversal and its coordinates
are four-tuplewise independent with symmetric marginals (expressed by the vanishing of the
character moments `E_ρ[χ_J]`, `1 ≤ |J| ≤ 4`), there is an odd `ψ` with values in `[-1,1]` such that
`E_ρ[Z_j ψ] = 1/√(3|B|)` for every `j ∈ B`.
-/

open Finset
open scoped symmDiff Nat

namespace FiniteOrderMixing

/-! ## Laws on finite blocks -/

/-- `ρ` is a probability density on the coordinates of `B` with respect to the uniform law. -/
structure IsLaw (B : Finset ℤ) (ρ : Config → ℝ) : Prop where
  dep : Dep ρ B
  nonneg : ∀ ω, 0 ≤ ρ ω
  avg_eq_one : avg B ρ = 1

/-- Invariance of `ρ` under the global sign reversal on `B`. -/
def IsEven (B : Finset ℤ) (ρ : Config → ℝ) : Prop := ∀ ω, ρ (flipOn B ω) = ρ ω

/-- The properties required of the auxiliary function `ψ_ρ` of Lemma `lem:bias`. -/
structure IsBias (B : Finset ℤ) (ρ ψ : Config → ℝ) : Prop where
  dep : Dep ψ B
  bound : ∀ ω, |ψ ω| ≤ 1
  odd : ∀ ω, ψ (flipOn B ω) = -ψ ω
  corr : ∀ j ∈ B, avg B (fun ω => ρ ω * Z j ω * ψ ω) = 1 / Real.sqrt (3 * B.card)

lemma flipOn_flipOn (B : Finset ℤ) (ω : Config) : flipOn B (flipOn B ω) = ω := by
  funext j; by_cases hj : j ∈ B <;> simp [flipOn, hj]

lemma Z_flipOn {B : Finset ℤ} {j : ℤ} (hj : j ∈ B) (ω : Config) :
    Z j (flipOn B ω) = -Z j ω := by
  cases h : ω j <;> simp [Z, flipOn, hj, h, spin]

lemma Dep.flipOn {F : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) :
    Dep (fun ω => F (FiniteOrderMixing.flipOn B ω)) B := fun ω ω' h =>
  hF _ _ fun j hj => by simp [FiniteOrderMixing.flipOn, hj, h j hj]

/-- An odd `ψ` has mean zero under an even law. -/
lemma IsBias.avg_eq_zero {B : Finset ℤ} {ρ ψ : Config → ℝ} (hψ : IsBias B ρ ψ)
    (hρ : IsEven B ρ) : avg B (fun ω => ρ ω * ψ ω) = 0 := by
  have h := avg_flipOn B (fun ω => ρ ω * ψ ω)
  simp only [hρ _, hψ.odd] at h
  rw [avg_congr (fun ω => by ring : ∀ ω, ρ ω * -ψ ω = -(ρ ω * ψ ω)), avg_neg] at h
  linarith

/-! ## Products of coordinates reduce to characters -/

/-- The set of indices occurring an odd number of times in a list. -/
def oddSet : List ℤ → Finset ℤ
  | [] => ∅
  | a :: l => {a} ∆ oddSet l

lemma chi_mul_self (A : Finset ℤ) (ω : Config) : chi A ω * chi A ω = 1 := by
  simp only [chi, ← Finset.prod_mul_distrib, Z_mul_self, Finset.prod_const_one]

lemma chi_symmDiff (A B : Finset ℤ) (ω : Config) : chi (A ∆ B) ω = chi A ω * chi B ω := by
  have hA : chi A ω = chi (A \ B) ω * chi (A ∩ B) ω := by
    rw [← chi_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]
  have hB : chi B ω = chi (B \ A) ω * chi (A ∩ B) ω := by
    rw [Finset.inter_comm, ← chi_union (Finset.disjoint_sdiff_inter B A),
      Finset.sdiff_union_inter]
  have hs : chi (A ∆ B) ω = chi (A \ B) ω * chi (B \ A) ω := by
    rw [symmDiff_def, Finset.sup_eq_union, chi_union disjoint_sdiff_sdiff]
  rw [hs, hA, hB]
  have := chi_mul_self (A ∩ B) ω
  calc chi (A \ B) ω * chi (B \ A) ω
      = chi (A \ B) ω * chi (B \ A) ω * (chi (A ∩ B) ω * chi (A ∩ B) ω) := by rw [this, mul_one]
    _ = _ := by ring

lemma prod_map_Z (l : List ℤ) (ω : Config) :
    (l.map fun j => Z j ω).prod = chi (oddSet l) ω := by
  induction l with
  | nil => simp [oddSet]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, oddSet, chi_symmDiff]
    simp [chi]

lemma card_oddSet_le (l : List ℤ) : (oddSet l).card ≤ l.length := by
  induction l with
  | nil => simp [oddSet]
  | cons a l ih =>
    simp only [oddSet, List.length_cons]
    calc ({a} ∆ oddSet l).card ≤ ({a} ∪ oddSet l).card :=
          Finset.card_le_card (by simpa using (symmDiff_le_sup (a := ({a} : Finset ℤ))
            (b := oddSet l)))
      _ ≤ ({a} : Finset ℤ).card + (oddSet l).card := Finset.card_union_le _ _
      _ ≤ l.length + 1 := by simp; omega

lemma oddSet_subset (l : List ℤ) : oddSet l ⊆ l.toFinset := by
  induction l with
  | nil => simp [oddSet]
  | cons a l ih =>
    simp only [oddSet, List.toFinset_cons]
    intro x hx
    have := (symmDiff_le_sup (a := ({a} : Finset ℤ)) (b := oddSet l)) hx
    simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | h
    · simp [h]
    · exact Finset.mem_insert_of_mem (ih h)

/-- A product of `p` coordinates is a character of a set of at most `p` of the indices. -/
lemma prod_Z_eq_chi {p : ℕ} (t : Fin p → ℤ) (ω : Config) :
    ∏ i, Z (t i) ω = chi (oddSet (List.ofFn t)) ω := by
  rw [← prod_map_Z, List.map_ofFn, List.prod_ofFn]
  rfl

lemma card_oddSet_ofFn {p : ℕ} (t : Fin p → ℤ) : (oddSet (List.ofFn t)).card ≤ p := by
  simpa using card_oddSet_le (List.ofFn t)

lemma oddSet_ofFn_subset {p : ℕ} (t : Fin p → ℤ) {B : Finset ℤ} (ht : ∀ i, t i ∈ B) :
    oddSet (List.ofFn t) ⊆ B := by
  intro x hx
  have := oddSet_subset _ hx
  rw [List.mem_toFinset, List.mem_ofFn] at this
  obtain ⟨i, rfl⟩ := this
  exact ht i

/-- Expansion of a power of a linear form in the coordinates. -/
lemma linform_pow (B : Finset ℤ) (a : ℤ → ℝ) (p : ℕ) (ω : Config) :
    (∑ j ∈ B, a j * Z j ω) ^ p = ∑ t ∈ Fintype.piFinset (fun _ : Fin p => B),
      (∏ i, a (t i)) * chi (oddSet (List.ofFn t)) ω := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib, prod_Z_eq_chi]

/-- **Moment matching.**  If the characters of at most `p` coordinates have the same expectations
under `ρ` as under the uniform law, then so do the `p`-th powers of linear forms. -/
lemma avg_mul_linform_pow {B : Finset ℤ} {ρ : Config → ℝ} (hρ : avg B ρ = 1) (p : ℕ)
    (hmom : ∀ K ⊆ B, K.Nonempty → K.card ≤ p → avg B (fun ω => ρ ω * chi K ω) = 0)
    (a : ℤ → ℝ) :
    avg B (fun ω => ρ ω * (∑ j ∈ B, a j * Z j ω) ^ p) =
      avg B (fun ω => (∑ j ∈ B, a j * Z j ω) ^ p) := by
  simp only [linform_pow, Finset.mul_sum]
  rw [avg_sum, avg_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htB : ∀ i, t i ∈ B := fun i => Fintype.mem_piFinset.1 ht i
  set K := oddSet (List.ofFn t)
  have hKB : K ⊆ B := oddSet_ofFn_subset t htB
  rw [avg_congr (fun ω => by ring : ∀ ω, ρ ω * ((∏ i, a (t i)) * chi K ω) =
    (∏ i, a (t i)) * (ρ ω * chi K ω)), avg_const_mul, avg_const_mul]
  congr 1
  rcases K.eq_empty_or_nonempty with hK | hK
  · rw [hK]
    have : chi ∅ = fun _ => (1 : ℝ) := funext chi_empty
    rw [this, avg_const]; simpa using hρ
  · rw [hmom K hKB hK (card_oddSet_ofFn t), avg_chi hKB hK]

/-! ## Second and fourth moments of linear forms -/

lemma avg_mul_Z_mul_Z {B : Finset ℤ} {ρ : Config → ℝ} (hρ : avg B ρ = 1)
    (hmom : ∀ K ⊆ B, K.Nonempty → K.card ≤ 2 → avg B (fun ω => ρ ω * chi K ω) = 0)
    {i j : ℤ} (hi : i ∈ B) (hj : j ∈ B) :
    avg B (fun ω => ρ ω * (Z i ω * Z j ω)) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij; simpa [Z_mul_self] using hρ
  · have : ∀ ω, Z i ω * Z j ω = chi {i, j} ω := fun ω => by simp [chi, hij]
    simp only [this]
    exact hmom _ (by simp [Finset.insert_subset_iff, hi, hj]) (by simp)
      (Finset.card_le_two)

lemma avg_mul_linform_sq {B : Finset ℤ} {ρ : Config → ℝ} (hρ : avg B ρ = 1)
    (hmom : ∀ K ⊆ B, K.Nonempty → K.card ≤ 2 → avg B (fun ω => ρ ω * chi K ω) = 0)
    (a : ℤ → ℝ) :
    avg B (fun ω => ρ ω * (∑ j ∈ B, a j * Z j ω) ^ 2) = ∑ j ∈ B, a j ^ 2 := by
  have : ∀ ω, ρ ω * (∑ j ∈ B, a j * Z j ω) ^ 2 =
      ∑ i ∈ B, ∑ j ∈ B, (a i * a j) * (ρ ω * (Z i ω * Z j ω)) := fun ω => by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [avg_congr this, avg_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [avg_sum]
  simp only [avg_const_mul]
  rw [Finset.sum_congr rfl fun j hj => by rw [avg_mul_Z_mul_Z hρ hmom hi hj]]
  simp [sq, hi]

/-- Elementary inequality behind the `L¹` lower bound:
`9 s² u² ≤ 6√3 s³ u + u⁴` for `u, s ≥ 0`, since the difference is `u (u - √3 s)² (u + 2√3 s)`. -/
lemma key_poly_ineq {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    9 * s ^ 2 * u ^ 2 ≤ 6 * Real.sqrt 3 * s ^ 3 * u + u ^ 4 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have key : 6 * Real.sqrt 3 * s ^ 3 * u + u ^ 4 - 9 * s ^ 2 * u ^ 2 =
      u * ((u - Real.sqrt 3 * s) ^ 2 * (u + 2 * Real.sqrt 3 * s)) := by
    have : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, h3]
    ring_nf
    rw [h3, this]
    ring
  have : 0 ≤ u * ((u - Real.sqrt 3 * s) ^ 2 * (u + 2 * Real.sqrt 3 * s)) := by positivity
  linarith

/-- `E_ρ|a·X| ≥ ‖a‖₂/√3` (inequality `eq:linear-form-lower-bound`). -/
lemma avg_abs_linform_ge {B : Finset ℤ} {ρ : Config → ℝ} (hρ : IsLaw B ρ)
    (hmom : ∀ K ⊆ B, K.Nonempty → K.card ≤ 4 → avg B (fun ω => ρ ω * chi K ω) = 0)
    (a : ℤ → ℝ) :
    Real.sqrt (∑ j ∈ B, a j ^ 2) / Real.sqrt 3 ≤
      avg B (fun ω => ρ ω * |∑ j ∈ B, a j * Z j ω|) := by
  set s2 := ∑ j ∈ B, a j ^ 2
  set s := Real.sqrt s2
  set Y := fun ω => ∑ j ∈ B, a j * Z j ω
  have hs2 : 0 ≤ s2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hss : s ^ 2 = s2 := Real.sq_sqrt hs2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hmom2 : ∀ K ⊆ B, K.Nonempty → K.card ≤ 2 → avg B (fun ω => ρ ω * chi K ω) = 0 :=
    fun K h1 h2 h3 => hmom K h1 h2 (by omega)
  have hE2 : avg B (fun ω => ρ ω * Y ω ^ 2) = s2 := avg_mul_linform_sq hρ.avg_eq_one hmom2 a
  have hE4 : avg B (fun ω => ρ ω * Y ω ^ 4) ≤ 3 * s2 ^ 2 := by
    rw [avg_mul_linform_pow hρ.avg_eq_one 4 hmom a]
    have := khintchine B a 2
    norm_num at this
    simpa [Y] using this
  have hE1 : 0 ≤ avg B (fun ω => ρ ω * |Y ω|) :=
    avg_nonneg fun ω => mul_nonneg (hρ.nonneg ω) (abs_nonneg _)
  rcases hs0.lt_or_eq with hpos | hzero
  · -- integrate the pointwise inequality against `ρ`
    have hpt : ∀ ω, ρ ω * (9 * s ^ 2 * Y ω ^ 2) ≤
        ρ ω * (6 * Real.sqrt 3 * s ^ 3 * |Y ω| + Y ω ^ 4) := fun ω => by
      have := key_poly_ineq hs0 (abs_nonneg (Y ω))
      rw [sq_abs, show |Y ω| ^ 4 = Y ω ^ 4 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at this
      exact mul_le_mul_of_nonneg_left this (hρ.nonneg ω)
    have hint := avg_mono (B := B) hpt
    rw [avg_congr (fun ω => by ring : ∀ ω, ρ ω * (9 * s ^ 2 * Y ω ^ 2) =
        (9 * s ^ 2) * (ρ ω * Y ω ^ 2)), avg_const_mul, hE2] at hint
    rw [avg_congr (fun ω => by ring : ∀ ω, ρ ω * (6 * Real.sqrt 3 * s ^ 3 * |Y ω| + Y ω ^ 4) =
        (6 * Real.sqrt 3 * s ^ 3) * (ρ ω * |Y ω|) + ρ ω * Y ω ^ 4)] at hint
    rw [show (fun ω => 6 * Real.sqrt 3 * s ^ 3 * (ρ ω * |Y ω|) + ρ ω * Y ω ^ 4) =
        (fun ω => 6 * Real.sqrt 3 * s ^ 3 * (ρ ω * |Y ω|)) + (fun ω => ρ ω * Y ω ^ 4) from rfl,
      avg_add, avg_const_mul] at hint
    have h3 : 0 < Real.sqrt 3 := by positivity
    rw [div_le_iff₀ h3]
    have hs4 : s2 ^ 2 = s ^ 4 := by rw [← hss]; ring
    have : 6 * s ^ 4 ≤ 6 * s ^ 3 * (avg B (fun ω => ρ ω * |Y ω|) * Real.sqrt 3) := by
      rw [← hss] at hint hE4; nlinarith
    have hs3 : 0 < 6 * s ^ 3 := by positivity
    have : s ^ 3 * s ≤ s ^ 3 * (avg B (fun ω => ρ ω * |Y ω|) * Real.sqrt 3) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · rw [← hzero]; simpa using hE1

/-! ## The biasing lemma -/

/-- The pattern of `ω` on `B`, as the set of coordinates of `B` where `ω` is `true`. -/
def pat (B : Finset ℤ) (ω : Config) : B.powerset :=
  ⟨B.filter (fun j => ω j = true), Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩

lemma pat_congr {B : Finset ℤ} {ω ω' : Config} (h : ∀ j ∈ B, ω j = ω' j) : pat B ω = pat B ω' := by
  apply Subtype.ext
  simp only [pat]
  exact Finset.filter_congr fun j hj => by rw [h j hj]

lemma Z_eq_of_pat {B : Finset ℤ} {j : ℤ} (hj : j ∈ B) (ω : Config) :
    Z j ω = if j ∈ (pat B ω).1 then 1 else -1 := by
  cases h : ω j <;> simp [Z, pat, hj, h]

/-- **Lemma `lem:bias`.** -/
theorem exists_bias {B : Finset ℤ} {ρ : Config → ℝ} (hρ : IsLaw B ρ) (heven : IsEven B ρ)
    (hmom : ∀ K ⊆ B, K.Nonempty → K.card ≤ 4 → avg B (fun ω => ρ ω * chi K ω) = 0) :
    ∃ ψ, IsBias B ρ ψ := by
  classical
  set c : ℝ := 1 / Real.sqrt (3 * B.card)
  let V := B → ℝ
  let P := B.powerset
  -- the linear map `g ↦ (E_ρ[Z_j g(pattern)])_j`
  let Φ : (P → ℝ) →ₗ[ℝ] V :=
    { toFun := fun g j => avg B (fun ω => ρ ω * Z j ω * g (pat B ω))
      map_add' := fun g g' => by
        funext j
        change _ = avg B _ + avg B _
        rw [← avg_add]
        exact avg_congr fun ω => by simp; ring
      map_smul' := fun r g => by
        funext j
        change _ = r * avg B _
        rw [← avg_const_mul]
        exact avg_congr fun ω => by rw [Pi.smul_apply, smul_eq_mul]; ring }
  let cube : Set (P → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-1) 1
  let K := Φ '' cube
  have hcube : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc
  have hKc : IsClosed K := (hcube.image Φ.continuous_of_finiteDimensional).isClosed
  have hKv : Convex ℝ K := (convex_pi fun _ _ => convex_Icc (-1) 1).linear_image Φ
  let v : V := fun _ => c
  have hv : v ∈ K := by
    by_contra hv
    obtain ⟨f, u, hfv, hK⟩ := geometric_hahn_banach_point_closed hKv hKc hv
    let a : ℤ → ℝ := fun j => if h : j ∈ B then f (Pi.single ⟨j, h⟩ 1) else 0
    have hf : ∀ w : V, f w = ∑ j ∈ B, a j * (if h : j ∈ B then w ⟨j, h⟩ else 0) := by
      intro w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [map_sum, ← Finset.sum_coe_sort B]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Pi.single i (w i) = w i • (Pi.single i 1 : V) := by
        rw [← Pi.single_smul]; simp
      rw [this, map_smul, smul_eq_mul]
      simp [a, mul_comm]
    -- the test function `g₀ = -sgn(a·Z)`
    let Yp : P → ℝ := fun T => ∑ j ∈ B, a j * (if j ∈ T.1 then 1 else -1)
    let g0 : P → ℝ := fun T => if 0 ≤ Yp T then -1 else 1
    have hg0 : g0 ∈ cube := fun T _ => by
      simp only [g0]; split_ifs <;> norm_num
    have hY : ∀ ω, (∑ j ∈ B, a j * Z j ω) = Yp (pat B ω) :=
      fun ω => Finset.sum_congr rfl fun j hj => by rw [Z_eq_of_pat hj]
    have hYg : ∀ ω, (∑ j ∈ B, a j * Z j ω) * g0 (pat B ω) = -|∑ j ∈ B, a j * Z j ω| := by
      intro ω; rw [hY]; simp only [g0]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.1 h)]; ring
    have hfΦ : f (Φ g0) = -avg B (fun ω => ρ ω * |∑ j ∈ B, a j * Z j ω|) := by
      rw [hf, ← avg_neg]
      have : ∀ j ∈ B, a j * (if h : j ∈ B then Φ g0 ⟨j, h⟩ else 0) =
          avg B (fun ω => a j * (ρ ω * Z j ω * g0 (pat B ω))) := fun j hj => by
        rw [dite_eq_left hj, avg_const_mul]; rfl
      rw [Finset.sum_congr rfl this, ← avg_sum]
      refine avg_congr fun ω => ?_
      rw [← mul_neg, ← hYg, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hlow := avg_abs_linform_ge hρ hmom a
    have hfv' : -(Real.sqrt (∑ j ∈ B, a j ^ 2) / Real.sqrt 3) ≤ f v := by
      have hsum : ∑ j ∈ B, a j * (if h : j ∈ B then v ⟨j, h⟩ else 0) = (∑ j ∈ B, a j) * c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j hj => by simp [hj, v]
      rw [hf, hsum]
      have hcs : (∑ j ∈ B, a j) ^ 2 ≤ B.card * ∑ j ∈ B, a j ^ 2 := by
        have := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) a
        simpa using this
      rcases B.eq_empty_or_nonempty with hB | hB
      · simp [hB]
      have hn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
      have habs : |∑ j ∈ B, a j| ≤ Real.sqrt B.card * Real.sqrt (∑ j ∈ B, a j ^ 2) := by
        rw [← Real.sqrt_mul hn.le, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hcs
      have hc : c = 1 / (Real.sqrt 3 * Real.sqrt B.card) := by
        simp only [c]; rw [Real.sqrt_mul (by norm_num)]
      rw [hc]
      have h3 : 0 < Real.sqrt 3 := by positivity
      have hn' : 0 < Real.sqrt B.card := Real.sqrt_pos.2 hn
      have hle : -(Real.sqrt B.card * Real.sqrt (∑ j ∈ B, a j ^ 2)) ≤ ∑ j ∈ B, a j := by
        have := neg_abs_le (∑ j ∈ B, a j); linarith
      calc -(Real.sqrt (∑ j ∈ B, a j ^ 2) / Real.sqrt 3)
          = -(Real.sqrt B.card * Real.sqrt (∑ j ∈ B, a j ^ 2)) /
              (Real.sqrt 3 * Real.sqrt B.card) := by
            rw [mul_comm (Real.sqrt 3) _, neg_div, mul_div_mul_left _ _ hn'.ne']
        _ ≤ (∑ j ∈ B, a j) / (Real.sqrt 3 * Real.sqrt B.card) :=
            div_le_div_of_nonneg_right hle (mul_pos h3 hn').le
        _ = (∑ j ∈ B, a j) * (1 / (Real.sqrt 3 * Real.sqrt B.card)) := by ring
    have := hK _ ⟨g0, hg0, rfl⟩
    rw [hfΦ] at this
    linarith
  obtain ⟨g, hg, hgv⟩ := hv
  refine ⟨fun ω => (g (pat B ω) - g (pat B (flipOn B ω))) / 2, ?_, ?_, ?_, ?_⟩
  · intro ω ω' h
    simp only
    rw [pat_congr h, pat_congr (fun j hj => by simp [flipOn, hj, h j hj] :
      ∀ j ∈ B, flipOn B ω j = flipOn B ω' j)]
  · intro ω
    have h1 := hg (pat B ω) (Set.mem_univ _)
    have h2 := hg (pat B (flipOn B ω)) (Set.mem_univ _)
    simp only [Set.mem_Icc] at h1 h2
    rw [abs_le]; constructor <;> linarith
  · intro ω; simp only [flipOn_flipOn]; ring
  · intro j hj
    have hΦ : avg B (fun ω => ρ ω * Z j ω * g (pat B ω)) = c := congrFun hgv ⟨j, hj⟩
    have hflip := avg_flipOn B (fun ω => ρ ω * Z j ω * g (pat B ω))
    simp only [heven _, Z_flipOn hj] at hflip
    have : ∀ ω, ρ ω * Z j ω * ((g (pat B ω) - g (pat B (flipOn B ω))) / 2) =
        (1 / 2) * (ρ ω * Z j ω * g (pat B ω)) + (1 / 2) * (ρ ω * -Z j ω * g (pat B (flipOn B ω)))
        := fun ω => by ring
    rw [avg_congr this]
    rw [show (fun ω => (1 / 2 : ℝ) * (ρ ω * Z j ω * g (pat B ω)) +
        (1 / 2) * (ρ ω * -Z j ω * g (pat B (flipOn B ω)))) =
        (fun ω => (1 / 2 : ℝ) * (ρ ω * Z j ω * g (pat B ω))) +
        (fun ω => (1 / 2) * (ρ ω * -Z j ω * g (pat B (flipOn B ω)))) from rfl,
      avg_add, avg_const_mul, avg_const_mul, hflip, hΦ]
    ring

end FiniteOrderMixing
