import FiniteOrderMixing.Basic

/-!
# Uniform averages over finitely many coordinates

All finite-dimensional block laws of the construction are encoded as *densities* with respect to
the uniform law on the coordinates of a finite set `B ⊆ ℤ`.  This file provides the calculus of the
uniform average `avg B F = 2^{-|B|} ∑_{x ∈ {-1,1}^B} F(x)`:

* `avgAt B F ω` averages `F` over the coordinates in `B`, keeping the other coordinates of `ω`;
* Fubini (`avgAt_union`), the product rule for functions of disjoint coordinate sets
  (`avg_union_mul`, `avg_biUnion_prod`), marginalisation (`avg_eq_of_dep`);
* invariance under the sign flip and under translations;
* orthogonality of the characters `χ_J = ∏_{j ∈ J} Z_j`.
-/

open Finset

namespace FiniteOrderMixing

/-- `F` depends only on the coordinates in the finite set `B`. -/
def Dep (F : Config → ℝ) (B : Finset ℤ) : Prop :=
  ∀ ω ω' : Config, (∀ j ∈ B, ω j = ω' j) → F ω = F ω'

lemma Dep.mono {F : Config → ℝ} {B C : Finset ℤ} (h : Dep F B) (hBC : B ⊆ C) : Dep F C :=
  fun ω ω' hω => h ω ω' fun j hj => hω j (hBC hj)

lemma dep_const (c : ℝ) (B : Finset ℤ) : Dep (fun _ => c) B := fun _ _ _ => rfl

lemma Dep.mul {F G : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) (hG : Dep G B) :
    Dep (F * G) B := fun ω ω' h => by simp [hF ω ω' h, hG ω ω' h]

lemma Dep.add {F G : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) (hG : Dep G B) :
    Dep (F + G) B := fun ω ω' h => by simp [hF ω ω' h, hG ω ω' h]

lemma Dep.sub {F G : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) (hG : Dep G B) :
    Dep (F - G) B := fun ω ω' h => by simp [hF ω ω' h, hG ω ω' h]

lemma Dep.const_mul {F : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) (c : ℝ) :
    Dep (fun ω => c * F ω) B := fun ω ω' h => by simp [hF ω ω' h]

lemma dep_prod {ι : Type*} (S : Finset ι) (F : ι → Config → ℝ) (B : Finset ℤ)
    (h : ∀ i ∈ S, Dep (F i) B) : Dep (fun ω => ∏ i ∈ S, F i ω) B := fun ω ω' hω =>
  Finset.prod_congr rfl fun i hi => h i hi ω ω' hω

lemma dep_sum {ι : Type*} (S : Finset ι) (F : ι → Config → ℝ) (B : Finset ℤ)
    (h : ∀ i ∈ S, Dep (F i) B) : Dep (fun ω => ∑ i ∈ S, F i ω) B := fun ω ω' hω =>
  Finset.sum_congr rfl fun i hi => h i hi ω ω' hω

lemma dep_Z (j : ℤ) : Dep (Z j) {j} := fun ω ω' h => by simp [Z, h j (by simp)]

lemma dep_Z_of_mem {j : ℤ} {B : Finset ℤ} (hj : j ∈ B) : Dep (Z j) B :=
  (dep_Z j).mono (by simpa using hj)

/-! ## Patching and averaging -/

/-- Overwrite the coordinates in `B` by the indicator of `T` (`true` on `T`). -/
def patch (B T : Finset ℤ) (ω : Config) : Config :=
  fun j => if j ∈ B then decide (j ∈ T) else ω j

/-- The constant configuration, used as background. -/
def allTrue : Config := fun _ => true

/-- Average of `F` over the coordinates in `B`, the other coordinates being those of `ω`. -/
noncomputable def avgAt (B : Finset ℤ) (F : Config → ℝ) (ω : Config) : ℝ :=
  (∑ T ∈ B.powerset, F (patch B T ω)) / 2 ^ B.card

/-- Uniform average of `F` over the coordinates in `B`. -/
noncomputable def avg (B : Finset ℤ) (F : Config → ℝ) : ℝ := avgAt B F allTrue

@[simp] lemma patch_empty (T : Finset ℤ) (ω : Config) : patch ∅ T ω = ω := by
  funext j; simp [patch]

lemma avgAt_empty (F : Config → ℝ) (ω : Config) : avgAt ∅ F ω = F ω := by
  simp [avgAt]

lemma patch_insert_insert {a : ℤ} {B T : Finset ℤ} (ha : a ∉ B) (_hT : T ⊆ B) (ω : Config) :
    patch (insert a B) (insert a T) ω = patch B T (Function.update ω a true) := by
  funext j
  by_cases hj : j = a
  · subst hj; simp [patch, ha]
  · by_cases hjB : j ∈ B <;> simp [patch, hj, hjB]

lemma patch_insert {a : ℤ} {B T : Finset ℤ} (ha : a ∉ B) (hT : T ⊆ B) (ω : Config) :
    patch (insert a B) T ω = patch B T (Function.update ω a false) := by
  funext j
  by_cases hj : j = a
  · subst hj
    have : j ∉ T := fun h => ha (hT h)
    simp [patch, ha, this]
  · by_cases hjB : j ∈ B <;> simp [patch, hj, hjB]

lemma avgAt_insert {a : ℤ} {B : Finset ℤ} (ha : a ∉ B) (F : Config → ℝ) (ω : Config) :
    avgAt (insert a B) F ω =
      (avgAt B F (Function.update ω a true) + avgAt B F (Function.update ω a false)) / 2 := by
  simp only [avgAt]
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
  have h1 : ∑ t ∈ B.powerset, F (patch (insert a B) t ω) =
      ∑ t ∈ B.powerset, F (patch B t (Function.update ω a false)) :=
    Finset.sum_congr rfl fun t ht => by rw [patch_insert ha (Finset.mem_powerset.1 ht)]
  have h2 : ∑ t ∈ B.powerset, F (patch (insert a B) (insert a t) ω) =
      ∑ t ∈ B.powerset, F (patch B t (Function.update ω a true)) :=
    Finset.sum_congr rfl fun t ht => by rw [patch_insert_insert ha (Finset.mem_powerset.1 ht)]
  rw [h1, h2]
  field_simp
  ring

lemma avgAt_congr {B : Finset ℤ} {F G : Config → ℝ} (h : ∀ ω, F ω = G ω) (ω : Config) :
    avgAt B F ω = avgAt B G ω := by
  simp [avgAt, h]

/-- The partial average does not depend on the coordinates that are averaged. -/
lemma avgAt_dep_compl {B : Finset ℤ} (F : Config → ℝ) {ω ω' : Config}
    (h : ∀ j ∉ B, ω j = ω' j) : avgAt B F ω = avgAt B F ω' := by
  simp only [avgAt]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  funext j
  by_cases hj : j ∈ B <;> simp [patch, hj, h]

/-- If `F` depends only on `B`, the partial average is the full average. -/
lemma avgAt_eq_avg {B : Finset ℤ} {F : Config → ℝ} (hF : Dep F B) (ω : Config) :
    avgAt B F ω = avg B F := by
  simp only [avg, avgAt]
  congr 1
  refine Finset.sum_congr rfl fun T _ => hF _ _ fun j hj => by simp [patch, hj]

/-- `avgAt B F` depends only on the coordinates outside `B` that `F` depends on. -/
lemma dep_avgAt {B C : Finset ℤ} {F : Config → ℝ} (hF : Dep F C) :
    Dep (avgAt B F) (C \ B) := by
  intro ω ω' h
  simp only [avgAt]
  congr 1
  refine Finset.sum_congr rfl fun T _ => hF _ _ fun j hj => ?_
  by_cases hjB : j ∈ B
  · simp [patch, hjB]
  · simp [patch, hjB, h j (Finset.mem_sdiff.2 ⟨hj, hjB⟩)]

/-- **Fubini** for disjoint coordinate sets. -/
lemma avgAt_union {B C : Finset ℤ} (hBC : Disjoint B C) (F : Config → ℝ) (ω : Config) :
    avgAt (B ∪ C) F ω = avgAt B (avgAt C F) ω := by
  induction B using Finset.induction_on generalizing ω with
  | empty => simp [avgAt_empty]
  | insert a B ha ih =>
    have haC : a ∉ C := Finset.disjoint_left.1 hBC (Finset.mem_insert_self a B)
    have hBC' : Disjoint B C := Finset.disjoint_of_subset_left (Finset.subset_insert a B) hBC
    have haBC : a ∉ B ∪ C := by simp [ha, haC]
    rw [Finset.insert_union, avgAt_insert haBC, avgAt_insert ha, ih hBC', ih hBC']

lemma avgAt_add {B : Finset ℤ} (F G : Config → ℝ) (ω : Config) :
    avgAt B (F + G) ω = avgAt B F ω + avgAt B G ω := by
  simp [avgAt, Finset.sum_add_distrib, add_div]

lemma avgAt_const_mul {B : Finset ℤ} (c : ℝ) (F : Config → ℝ) (ω : Config) :
    avgAt B (fun ω => c * F ω) ω = c * avgAt B F ω := by
  simp [avgAt, ← Finset.mul_sum, mul_div_assoc]

lemma avgAt_const {B : Finset ℤ} (c : ℝ) (ω : Config) : avgAt B (fun _ => c) ω = c := by
  simp [avgAt, Finset.card_powerset]

/-- Functions that do not depend on `B` come out of the partial average. -/
lemma avgAt_mul_left {B : Finset ℤ} {F : Config → ℝ} (hF : ∀ ω ω', (∀ j ∉ B, ω j = ω' j) →
    F ω = F ω') (G : Config → ℝ) (ω : Config) :
    avgAt B (F * G) ω = F ω * avgAt B G ω := by
  simp only [avgAt, Pi.mul_apply]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [hF _ ω fun j hj => by simp [patch, hj]]

lemma avg_add (B : Finset ℤ) (F G : Config → ℝ) : avg B (F + G) = avg B F + avg B G :=
  avgAt_add F G _

lemma avg_const_mul (B : Finset ℤ) (c : ℝ) (F : Config → ℝ) :
    avg B (fun ω => c * F ω) = c * avg B F := avgAt_const_mul c F _

lemma avg_const (B : Finset ℤ) (c : ℝ) : avg B (fun _ => c) = c := avgAt_const c _

lemma avg_congr {B : Finset ℤ} {F G : Config → ℝ} (h : ∀ ω, F ω = G ω) : avg B F = avg B G :=
  avgAt_congr h _

lemma avg_neg (B : Finset ℤ) (F : Config → ℝ) : avg B (fun ω => -F ω) = -avg B F := by
  have := avg_const_mul B (-1) F
  simpa using this

lemma avg_sub (B : Finset ℤ) (F G : Config → ℝ) : avg B (F - G) = avg B F - avg B G := by
  have h := avg_add B F (fun ω => -G ω)
  rw [avg_neg] at h
  rw [← sub_eq_add_neg] at h
  rw [← h]
  exact avg_congr fun ω => by simp [sub_eq_add_neg]

lemma avg_sum {ι : Type*} (B : Finset ℤ) (S : Finset ι) (F : ι → Config → ℝ) :
    avg B (fun ω => ∑ i ∈ S, F i ω) = ∑ i ∈ S, avg B (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using avg_const B 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ← ih, ← avg_add]
    exact avg_congr fun ω => by simp [Finset.sum_insert ha]

lemma avgAt_mono {B : Finset ℤ} {F G : Config → ℝ} (h : ∀ ω, F ω ≤ G ω) (ω : Config) :
    avgAt B F ω ≤ avgAt B G ω := by
  simp only [avgAt]
  gcongr with T _
  exact h _

lemma avg_mono {B : Finset ℤ} {F G : Config → ℝ} (h : ∀ ω, F ω ≤ G ω) : avg B F ≤ avg B G :=
  avgAt_mono h _

lemma avg_nonneg {B : Finset ℤ} {F : Config → ℝ} (h : ∀ ω, 0 ≤ F ω) : 0 ≤ avg B F := by
  simpa [avg_const] using avg_mono (B := B) (F := fun _ => 0) h

lemma abs_avg_le {B : Finset ℤ} (F : Config → ℝ) : |avg B F| ≤ avg B (fun ω => |F ω|) := by
  rw [abs_le]
  constructor
  · rw [← avg_neg]; exact avg_mono fun ω => neg_abs_le _
  · exact avg_mono fun ω => le_abs_self _

/-- If `F` does not depend on the coordinates of `C \ B`, averaging over `C` is averaging over
`B`. -/
lemma avg_eq_of_dep {B C : Finset ℤ} {F : Config → ℝ} (hF : Dep F B) (hBC : B ⊆ C) :
    avg C F = avg B F := by
  have hC : C = B ∪ (C \ B) := by rw [Finset.union_sdiff_of_subset hBC]
  have hd : Disjoint B (C \ B) := Finset.disjoint_sdiff
  simp only [avg]
  rw [hC, avgAt_union hd]
  congr 1
  funext ω
  have : ∀ T : Finset ℤ, F (patch (C \ B) T ω) = F ω := fun T =>
    hF _ _ fun j hj => by simp [patch, hj]
  simp only [avgAt, this, Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Product rule** for functions of disjoint sets of coordinates. -/
lemma avg_union_mul {B C : Finset ℤ} (hBC : Disjoint B C) {F G : Config → ℝ}
    (hF : Dep F B) (hG : Dep G C) : avg (B ∪ C) (F * G) = avg B F * avg C G := by
  simp only [avg]
  rw [avgAt_union hBC]
  have h1 : ∀ ω, avgAt C (F * G) ω = F ω * avg C G := fun ω => by
    rw [avgAt_mul_left (fun ω ω' h => hF ω ω' fun j hj =>
      h j (Finset.disjoint_left.1 hBC hj)), avgAt_eq_avg hG]
  rw [avgAt_congr h1]
  simp only [avg]
  rw [show (fun ω => F ω * avgAt C G allTrue) = fun ω => avgAt C G allTrue * F ω from
    funext fun ω => mul_comm _ _, avgAt_const_mul, mul_comm]

/-- Product rule over a finite pairwise-disjoint family. -/
lemma avg_biUnion_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (B : ι → Finset ℤ)
    (hdisj : (S : Set ι).PairwiseDisjoint B) (F : ι → Config → ℝ)
    (hF : ∀ i ∈ S, Dep (F i) (B i)) :
    avg (S.biUnion B) (fun ω => ∏ i ∈ S, F i ω) = ∏ i ∈ S, avg (B i) (F i) := by
  induction S using Finset.induction_on with
  | empty => simpa using avg_const ∅ 1
  | insert a S ha ih =>
    have hdisj' : (S : Set ι).PairwiseDisjoint B :=
      hdisj.subset (by simp [Set.subset_insert])
    have hd : Disjoint (B a) (S.biUnion B) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    have : (fun ω => ∏ i ∈ insert a S, F i ω) = F a * fun ω => ∏ i ∈ S, F i ω :=
      funext fun ω => by simp [Finset.prod_insert ha]
    rw [this, avg_union_mul hd (hF a (by simp))
      (dep_prod S F _ fun i hi => (hF i (by simp [hi])).mono (Finset.subset_biUnion_of_mem B hi)),
      ih hdisj' fun i hi => hF i (by simp [hi])]

/-! ## Sign flip -/

/-- Reverse all the signs in `B`. -/
def flipOn (B : Finset ℤ) (ω : Config) : Config := fun j => if j ∈ B then !ω j else ω j

lemma avg_flipOn (B : Finset ℤ) (F : Config → ℝ) : avg B (fun ω => F (flipOn B ω)) = avg B F := by
  simp only [avg, avgAt]
  congr 1
  refine Finset.sum_nbij' (fun T => B \ T) (fun T => B \ T) ?_ ?_ ?_ ?_ ?_
  · intro T _; simp
  · intro T _; simp
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact Finset.sdiff_sdiff_eq_self hT
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact Finset.sdiff_sdiff_eq_self hT
  · intro T _
    congr 1
    funext j
    by_cases hj : j ∈ B <;> simp [flipOn, patch, hj]

/-! ## Translations -/

/-- Translation of configurations: `(τ_m ω)_j = ω_{j+m}`. -/
def transl (m : ℤ) (ω : Config) : Config := fun j => ω (j + m)

@[simp] lemma transl_apply (m : ℤ) (ω : Config) (j : ℤ) : transl m ω j = ω (j + m) := rfl

lemma transl_zero (ω : Config) : transl 0 ω = ω := by funext j; simp

lemma transl_transl (m n : ℤ) (ω : Config) : transl m (transl n ω) = transl (m + n) ω := by
  funext j; simp [add_assoc]

/-- Translate a finite set: `B ↦ B + m`. -/
def tr (m : ℤ) (B : Finset ℤ) : Finset ℤ := B.map (addRightEmbedding m)

@[simp] lemma mem_tr {m j : ℤ} {B : Finset ℤ} : j ∈ tr m B ↔ j - m ∈ B := by
  simp only [tr, Finset.mem_map, addRightEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa using hi
  · intro h; exact ⟨j - m, h, by ring⟩

@[simp] lemma card_tr (m : ℤ) (B : Finset ℤ) : (tr m B).card = B.card := by simp [tr]

lemma Dep.transl {F : Config → ℝ} {B : Finset ℤ} (hF : Dep F B) (m : ℤ) :
    Dep (fun ω => F (FiniteOrderMixing.transl m ω)) (tr m B) := fun ω ω' h =>
  hF _ _ fun j hj => by simpa using h (j + m) (by simpa using hj)

lemma Dep.of_transl {F : Config → ℝ} {B : Finset ℤ} (m : ℤ)
    (hF : Dep (fun ω => F (FiniteOrderMixing.transl m ω)) (tr m B)) : Dep F B := by
  intro ω ω' h
  have := hF (FiniteOrderMixing.transl (-m) ω) (FiniteOrderMixing.transl (-m) ω') fun j hj => by
    simp only [transl_apply]; exact h _ (by simpa [sub_eq_add_neg] using hj)
  simpa [transl_transl, transl_zero] using this

/-- Averages are translation invariant. -/
lemma avg_transl (m : ℤ) (B : Finset ℤ) (F : Config → ℝ) :
    avg (tr m B) (fun ω => F (transl m ω)) = avg B F := by
  simp only [avg, avgAt, card_tr]
  congr 1
  refine Finset.sum_nbij' (fun T => tr (-m) T) (fun T => tr m T) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    intro j hj
    rw [mem_tr] at hj
    have := hT hj
    rw [mem_tr] at this
    simpa [sub_eq_add_neg] using this
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    intro j hj
    rw [mem_tr] at hj ⊢
    exact hT hj
  · intro T _; ext j; simp [mem_tr]
  · intro T _; ext j; simp [mem_tr]
  · intro T _
    congr 1
    funext j
    simp [patch, allTrue, mem_tr]

/-! ## Characters -/

/-- The character `χ_J = ∏_{j ∈ J} Z_j`. -/
noncomputable def chi (J : Finset ℤ) (ω : Config) : ℝ := ∏ j ∈ J, Z j ω

lemma dep_chi (J : Finset ℤ) : Dep (chi J) J :=
  dep_prod J (fun j => Z j) J fun _ hj => dep_Z_of_mem hj

lemma abs_chi (J : Finset ℤ) (ω : Config) : |chi J ω| = 1 := by
  simp [chi, Finset.abs_prod, Z, abs_spin]

lemma chi_union {J K : Finset ℤ} (h : Disjoint J K) (ω : Config) :
    chi (J ∪ K) ω = chi J ω * chi K ω := by
  simp [chi, Finset.prod_union h]

@[simp] lemma chi_empty (ω : Config) : chi ∅ ω = 1 := by simp [chi]

lemma Z_update_true (a : ℤ) (ω : Config) : Z a (Function.update ω a true) = 1 := by simp [Z]
lemma Z_update_false (a : ℤ) (ω : Config) : Z a (Function.update ω a false) = -1 := by simp [Z]

/-- A function linear in a coordinate `a ∈ B` it multiplies averages to zero:
`avg_B(G · Z_a) = 0` whenever `G` does not depend on `a`. -/
lemma avg_mul_Z_eq_zero {B : Finset ℤ} {a : ℤ} (ha : a ∈ B) {G : Config → ℝ}
    (hG : ∀ ω ω', (∀ j ≠ a, ω j = ω' j) → G ω = G ω') :
    avg B (fun ω => G ω * Z a ω) = 0 := by
  have hB : B = insert a (B.erase a) := (Finset.insert_erase ha).symm
  simp only [avg]
  rw [hB, avgAt_insert (Finset.notMem_erase a B)]
  have : ∀ ω, G (Function.update ω a true) * Z a (Function.update ω a true) =
      -(G (Function.update ω a false) * Z a (Function.update ω a false)) := fun ω => by
    simp only [Z_update_true, Z_update_false]
    rw [hG (Function.update ω a true) (Function.update ω a false) fun j hj => by
      simp [Function.update_of_ne hj]]
    ring
  have h2 : avgAt (B.erase a) (fun ω => G ω * Z a ω) (Function.update allTrue a true) =
      -avgAt (B.erase a) (fun ω => G ω * Z a ω) (Function.update allTrue a false) := by
    simp only [avgAt, ← neg_div, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => by
      have := Finset.mem_powerset.1 hT h; simp at this
    have e1 : patch (B.erase a) T (Function.update allTrue a true) =
        Function.update (patch (B.erase a) T (Function.update allTrue a true)) a true := by
      funext j; by_cases hj : j = a
      · subst hj; simp [patch]
      · simp [hj]
    have e2 : patch (B.erase a) T (Function.update allTrue a false) =
        Function.update (patch (B.erase a) T (Function.update allTrue a true)) a false := by
      funext j; by_cases hj : j = a
      · subst hj; simp [patch]
      · by_cases hjB : j ∈ B.erase a <;> simp [patch, hj, hjB]
    rw [e2]
    conv_lhs => rw [e1]
    exact this _
  rw [h2]; ring

/-- **Orthogonality of characters.** -/
lemma avg_chi {B J : Finset ℤ} (hJB : J ⊆ B) (hJ : J.Nonempty) : avg B (chi J) = 0 := by
  obtain ⟨a, ha⟩ := hJ
  have : ∀ ω, chi J ω = chi (J.erase a) ω * Z a ω := fun ω => by
    simp only [chi]; rw [← Finset.prod_erase_mul J _ ha]
  rw [avg_congr this]
  refine avg_mul_Z_eq_zero (hJB ha) fun ω ω' h => ?_
  exact dep_chi _ _ _ fun j hj => h j (Finset.ne_of_mem_erase hj)

/-- Products of coordinates reduce to characters: `Z_j^2 = 1`. -/
lemma Z_mul_self (j : ℤ) (ω : Config) : Z j ω * Z j ω = 1 := by
  have := spin_sq (ω j); simpa [Z, sq] using this

end FiniteOrderMixing
