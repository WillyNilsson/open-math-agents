import FormalConjectures.OptimizationConstants.«1a»
import C1aUpper.Kron

/-!
# Step-function upper bound for `Constant1a.C1a`

For `a : ℕ → ℕ` on `N` steps of width `h = 1 / (2 N)` over `(-1/4, 1/4]`, the autoconvolution of
the step function is at most `h * M` whenever every discrete autoconvolution value is at most `M`.
Hence `C1a ≤ 2 N M / S ^ 2`.
-/

namespace C1aUpper

open MeasureTheory Set Finset

/-- The `k`-th step cell `(-1/4 + k h, -1/4 + (k + 1) h]`. -/
def cell (h : ℝ) (k : ℕ) : Set ℝ := Ioc (-1 / 4 + k * h) (-1 / 4 + (k + 1) * h)

/-- The step function with heights `a i` on the cells `i < N`. -/
noncomputable def stepF (N : ℕ) (a : ℕ → ℕ) (h : ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ range N, (cell h i).indicator (fun _ => (a i : ℝ)) x

lemma cell_meas (h : ℝ) (k : ℕ) : MeasurableSet (cell h k) := measurableSet_Ioc

lemma vol_cell (h : ℝ) (k : ℕ) : volume (cell h k) = ENNReal.ofReal h := by
  rw [cell, Real.volume_Ioc]; congr 1; ring

lemma cell_disj {h : ℝ} (hh : 0 < h) {k l : ℕ} (hkl : k ≠ l) : Disjoint (cell h k) (cell h l) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [cell, Set.mem_Ioc] at hx hx'
  have h1 : (k : ℝ) * h < (l + 1) * h := by linarith
  have h2 : (l : ℝ) * h < (k + 1) * h := by linarith
  have h1' : (k : ℝ) < l + 1 := lt_of_mul_lt_mul_right h1 hh.le
  have h2' : (l : ℝ) < k + 1 := lt_of_mul_lt_mul_right h2 hh.le
  have : k < l + 1 := by exact_mod_cast h1'
  have : l < k + 1 := by exact_mod_cast h2'
  omega

lemma stepF_nonneg (N : ℕ) (a : ℕ → ℕ) (h : ℝ) : 0 ≤ stepF N a h := by
  intro x
  apply Finset.sum_nonneg
  intro i _
  apply Set.indicator_nonneg
  intro _ _; positivity

lemma stepF_meas (N : ℕ) (a : ℕ → ℕ) (h : ℝ) : Measurable (stepF N a h) := by
  unfold stepF
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (cell_meas h i)

lemma stepF_memLp (N : ℕ) (a : ℕ → ℕ) (h : ℝ) : MemLp (stepF N a h) 2 := by
  unfold stepF
  apply memLp_finsetSum
  intro i _
  apply memLp_indicator_const 2 (cell_meas h i)
  right; rw [vol_cell]; exact ENNReal.ofReal_ne_top

lemma stepF_integral (N : ℕ) (hN : 0 < N) (a : ℕ → ℕ) :
    ∫ x in (-1 / 4)..(1 / 4), stepF N a (1 / (2 * N)) x
      = (1 / (2 * N)) * (∑ i ∈ range N, (a i : ℝ)) := by
  set h : ℝ := 1 / (2 * N) with hdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 1 / 2 := by rw [hdef]; field_simp
  rw [intervalIntegral.integral_of_le (by norm_num)]
  unfold stepF
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ (cell_meas h i)]
    have hsub : cell h i ⊆ Ioc (-1 / 4) (1 / 4) := by
      have hi' : (i : ℝ) + 1 ≤ N := by
        have := Finset.mem_range.mp hi
        exact_mod_cast this
      intro x hx
      simp only [cell, Set.mem_Ioc] at hx ⊢
      constructor
      · have : 0 ≤ (i : ℝ) * h := by positivity
        linarith
      · have : ((i : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hi' hh.le
        linarith
    rw [Measure.real, Measure.restrict_apply (cell_meas h i), Set.inter_eq_left.mpr hsub,
      vol_cell, ENNReal.toReal_ofReal hh.le, smul_eq_mul]
  · intro i _
    rw [integrable_indicator_iff (cell_meas h i)]
    exact integrableOn_const (by
      rw [Measure.restrict_apply (cell_meas h i)]
      exact ne_top_of_le_ne_top (by rw [vol_cell]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_left))

/-- Pairwise overlap set: `x ∈ cell i` and `t - x ∈ cell j`. -/
def pairSet (h t : ℝ) (i j : ℕ) : Set ℝ := cell h i ∩ {x | t - x ∈ cell h j}

lemma pairSet_meas (h t : ℝ) (i j : ℕ) : MeasurableSet (pairSet h t i j) :=
  (cell_meas h i).inter ((cell_meas h j).preimage (measurable_const.sub measurable_id))

lemma pairSet_shift (h t : ℝ) (i j : ℕ) :
    pairSet h t i j = (fun x => x + (-(i * h))) ⁻¹' pairSet h t 0 (i + j) := by
  ext x
  simp only [pairSet, cell, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  push_cast
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma vol_pairSet (h t : ℝ) (i j : ℕ) :
    volume (pairSet h t i j) = volume (pairSet h t 0 (i + j)) := by
  rw [pairSet_shift, measure_preimage_add_right]

lemma sum_vol_pairSet {h : ℝ} (hh : 0 < h) (t : ℝ) (K : ℕ) :
    ∑ k ∈ range K, volume (pairSet h t 0 k) ≤ ENNReal.ofReal h := by
  rw [← measure_biUnion_finset]
  · calc volume (⋃ k ∈ range K, pairSet h t 0 k) ≤ volume (cell h 0) := by
          apply measure_mono
          intro x hx
          simp only [mem_iUnion] at hx
          obtain ⟨k, _, hk⟩ := hx
          exact hk.1
      _ = ENNReal.ofReal h := vol_cell h 0
  · intro k _ l _ hkl
    exact Disjoint.mono (fun x hx => hx.2) (fun x hx => hx.2)
      (Disjoint.preimage _ (cell_disj hh hkl))
  · intro k _; exact pairSet_meas h t 0 k

lemma integrand_eq (N : ℕ) (a : ℕ → ℕ) (h t x : ℝ) :
    ENNReal.ofReal (stepF N a h (t - x) * stepF N a h x)
      = ∑ i ∈ range N, ∑ j ∈ range N,
          ((a i * a j : ℕ) : ENNReal) * (pairSet h t i j).indicator 1 x := by
  unfold stepF
  rw [mul_comm, Finset.sum_mul_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hx : x ∈ cell h i <;> by_cases hy : t - x ∈ cell h j <;>
        simp [Set.indicator, pairSet, hx, hy, ENNReal.ofReal_mul]
    · intro j _
      apply mul_nonneg <;> apply Set.indicator_nonneg <;> intro _ _ <;> positivity
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg <;> apply Set.indicator_nonneg <;> intro _ _ <;> positivity

lemma autoconv_le (N : ℕ) (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (M : ℕ)
    (hM : ∀ m < 2 * N, conv N a m ≤ M) (t : ℝ) :
    ∫ x, stepF N a h (t - x) * stepF N a h x ≤ h * M := by
  have hmeas : Measurable fun x => stepF N a h (t - x) * stepF N a h x :=
    ((stepF_meas N a h).comp (measurable_const.sub measurable_id)).mul (stepF_meas N a h)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => mul_nonneg (stepF_nonneg N a h _) (stepF_nonneg N a h _))
    hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  simp_rw [integrand_eq]
  rw [lintegral_finsetSum (range N) (f := fun i x => ∑ j ∈ range N,
      ((a i * a j : ℕ) : ENNReal) * (pairSet h t i j).indicator 1 x)
    (fun i _ => Finset.measurable_sum _ (fun j _ =>
      (measurable_one.indicator (pairSet_meas h t i j)).const_mul _))]
  have hL : ∀ i ∈ range N, ∫⁻ x, ∑ j ∈ range N,
        ((a i * a j : ℕ) : ENNReal) * (pairSet h t i j).indicator 1 x
      = ∑ j ∈ range N, ((a i * a j : ℕ) : ENNReal) * volume (pairSet h t 0 (i + j)) := by
    intro i _
    rw [lintegral_finsetSum (range N) (f := fun j x =>
        ((a i * a j : ℕ) : ENNReal) * (pairSet h t i j).indicator 1 x)
      (fun j _ => (measurable_one.indicator (pairSet_meas h t i j)).const_mul _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [lintegral_const_mul _ (measurable_one.indicator (pairSet_meas h t i j)),
      lintegral_indicator_one (pairSet_meas h t i j), vol_pairSet]
  rw [Finset.sum_congr rfl hL]
  set L : ℕ → ENNReal := fun k => volume (pairSet h t 0 k) with hLdef
  have hre : ∑ i ∈ range N, ∑ j ∈ range N, ((a i * a j : ℕ) : ENNReal) * L (i + j)
      = ∑ k ∈ range (2 * N), (conv N a k : ENNReal) * L k := by
    have h1 : ∀ i ∈ range N, ∀ j ∈ range N, ((a i * a j : ℕ) : ENNReal) * L (i + j)
        = ∑ k ∈ range (2 * N), if i + j = k then ((a i * a j : ℕ) : ENNReal) * L k else 0 := by
      intro i hi j hj
      rw [Finset.sum_ite_eq, if_pos (by simp at hi hj ⊢; omega)]
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [conv, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> simp
  rw [hre]
  calc ∑ k ∈ range (2 * N), (conv N a k : ENNReal) * L k
      ≤ ∑ k ∈ range (2 * N), (M : ENNReal) * L k := by
        apply Finset.sum_le_sum
        intro k hk
        gcongr
        exact_mod_cast hM k (Finset.mem_range.mp hk)
    _ = (M : ENNReal) * ∑ k ∈ range (2 * N), L k := by rw [Finset.mul_sum]
    _ ≤ (M : ENNReal) * ENNReal.ofReal h := by
        gcongr; exact sum_vol_pairSet hh t _
    _ = ENNReal.ofReal (h * M) := by
        rw [ENNReal.ofReal_mul hh.le, ENNReal.ofReal_natCast, mul_comm]

/-- **Step-function upper bound.** -/
theorem C1a_le_of_steps (N : ℕ) (hN : 0 < N) (a : ℕ → ℕ) (M S0 : ℕ) (hS0 : 0 < S0)
    (hS : S0 ≤ ∑ i ∈ range N, a i) (hM : ∀ m < 2 * N, conv N a m ≤ M) :
    Constant1a.C1a ≤ (2 * N * M : ℝ) / (S0 : ℝ) ^ 2 := by
  set h : ℝ := 1 / (2 * N) with hdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < h := by positivity
  have hS0r : (0 : ℝ) < S0 := by exact_mod_cast hS0
  have hSr : (S0 : ℝ) ≤ ∑ i ∈ range N, (a i : ℝ) := by exact_mod_cast hS
  set S : ℝ := ∑ i ∈ range N, (a i : ℝ) with hSdef
  unfold Constant1a.C1a
  apply Real.sSup_le _ (by positivity)
  intro C hC
  have hsup : sSup {∫ x, stepF N a h (t - x) * stepF N a h x | t ∈ Icc (-1 / 2 : ℝ) (1 / 2)}
      ≤ h * M := by
    apply Real.sSup_le _ (by positivity)
    rintro _ ⟨t, _, rfl⟩
    exact autoconv_le N a hh M hM t
  have key := hC (stepF_nonneg N a h) (stepF_memLp N a h)
  rw [stepF_integral N hN a] at key
  have key2 : C * (h * S) ^ 2 ≤ h * M := le_trans key hsup
  rw [le_div_iff₀ (by positivity)]
  have hMr : (0 : ℝ) ≤ M := by positivity
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * (S0 : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (by positivity)
    have : (0 : ℝ) ≤ 2 * N * M := by positivity
    linarith
  · have h2 : C * (S0 : ℝ) ^ 2 ≤ C * S ^ 2 := by
      gcongr
    have h3 : C * S ^ 2 * h ≤ M := by
      have : h * (C * S ^ 2 * h) ≤ h * M := by nlinarith
      exact le_of_mul_le_mul_left this hh
    have h4 : (2 * N : ℝ) * h = 1 := by rw [hdef]; field_simp
    have h5 : C * S ^ 2 ≤ 2 * N * M := by
      have : C * S ^ 2 = (C * S ^ 2 * h) * (2 * N) := by
        rw [mul_assoc (C * S ^ 2), mul_comm h, h4, mul_one]
      rw [this]
      have : (0 : ℝ) ≤ 2 * N := by positivity
      nlinarith
    linarith

end C1aUpper
