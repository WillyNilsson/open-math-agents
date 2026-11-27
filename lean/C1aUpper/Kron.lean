import Mathlib

/-!
# Kronecker substitution certificate for discrete autoconvolutions

Pure `ℕ` lemmas. A vector `a` is stored as the base-`B` digits of one number `A`.
One multiplication `A * A` then encodes every autoconvolution value, and
a divide-and-conquer digit check bounds all of them.
-/

namespace C1aUpper

open Finset

/-- Discrete autoconvolution of `a` restricted to indices `< N`. -/
def conv (N : ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ range N, ∑ j ∈ range N, if i + j = m then a i * a j else 0

/-- The `i`-th base-`B` digit of `Y`. -/
def digit (B Y i : ℕ) : ℕ := Y / B ^ i % B

/-- Divide-and-conquer check that the lowest `n` base-`B` digits of `Y` are all `≤ T`. -/
def chk (B T : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, Y, n =>
    if n ≤ 1 then (n == 0 || Nat.ble (Y % B) T)
    else chk B T fuel (Y % B ^ (n / 2)) (n / 2) && chk B T fuel (Y / B ^ (n / 2)) (n - n / 2)

/-- Divide-and-conquer sum of the lowest `n` base-`B` digits of `Y` (a lower bound if fuel runs
out). -/
def dsum (B : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, Y, n =>
    if n ≤ 1 then (if n = 0 then 0 else Y % B)
    else dsum B fuel (Y % B ^ (n / 2)) (n / 2) + dsum B fuel (Y / B ^ (n / 2)) (n - n / 2)

/-- Horner packing of a list of chunks with a fixed bit shift. -/
def packL (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + 2 ^ s * packL s cs

lemma digit_mod {B Y h m : ℕ} (hm : m < h) : digit B (Y % B ^ h) m = digit B Y m := by
  unfold digit
  have hh : B ^ h = B ^ m * B ^ (h - m) := by rw [← pow_add]; congr 1; omega
  rw [hh, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self B (by omega)

lemma digit_div {B Y h m : ℕ} : digit B (Y / B ^ h) m = digit B Y (h + m) := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, ← pow_add]

lemma digit_zero {B Y : ℕ} : digit B Y 0 = Y % B := by simp [digit]

theorem chk_sound (B T : ℕ) : ∀ (fuel Y n : ℕ), chk B T fuel Y n = true →
    ∀ m < n, digit B Y m ≤ T := by
  intro fuel
  induction fuel with
  | zero => intro Y n h; simp [chk] at h
  | succ fuel ih =>
    intro Y n h m hm
    simp only [chk] at h
    split_ifs at h with hn
    · have hm0 : m = 0 := by omega
      subst hm0
      have hn1 : n ≠ 0 := by omega
      simp [hn1] at h
      rw [digit_zero]; exact h
    · rw [Bool.and_eq_true] at h
      by_cases hmh : m < n / 2
      · rw [← digit_mod hmh]; exact ih _ _ h.1 m hmh
      · have := ih _ _ h.2 (m - n / 2) (by omega)
        rw [digit_div] at this
        rwa [show n / 2 + (m - n / 2) = m by omega] at this

theorem dsum_le (B : ℕ) : ∀ (fuel Y n : ℕ), dsum B fuel Y n ≤ ∑ m ∈ range n, digit B Y m := by
  intro fuel
  induction fuel with
  | zero => intro Y n; simp [dsum]
  | succ fuel ih =>
    intro Y n
    simp only [dsum]
    split_ifs with hn hn0
    · simp
    · have : n = 1 := by omega
      subst this; simp [digit_zero]
    · have hsplit : n = n / 2 + (n - n / 2) := by omega
      conv_rhs => rw [hsplit, Finset.sum_range_add]
      gcongr
      · calc dsum B fuel (Y % B ^ (n / 2)) (n / 2)
            ≤ ∑ m ∈ range (n / 2), digit B (Y % B ^ (n / 2)) m := ih _ _
          _ = ∑ m ∈ range (n / 2), digit B Y m := by
            apply Finset.sum_congr rfl
            intro m hm; exact digit_mod (Finset.mem_range.mp hm)
      · calc dsum B fuel (Y / B ^ (n / 2)) (n - n / 2)
            ≤ ∑ m ∈ range (n - n / 2), digit B (Y / B ^ (n / 2)) m := ih _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m _; exact digit_div

theorem sum_digit_pow (B Y : ℕ) : ∀ n, ∑ i ∈ range n, digit B Y i * B ^ i = Y % B ^ n := by
  intro n
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, digit]; ring

theorem digit_of_sum (B : ℕ) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ m < n, d m < B) →
    ∀ k < n, digit B (∑ m ∈ range n, d m * B ^ m) k = d k := by
  intro n
  induction n with
  | zero => intro d _ k hk; omega
  | succ n ih =>
    intro d hd k hk
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hd 0 (by omega))
    have hrepr : ∑ m ∈ range (n + 1), d m * B ^ m
        = d 0 + B * ∑ m ∈ range n, d (m + 1) * B ^ m := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      rw [add_comm]; congr 1
      · simp
      · apply Finset.sum_congr rfl; intro m _; ring
    rw [hrepr]
    have hd0 := hd 0 (by omega)
    rcases k with _ | k
    · rw [digit_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
    · have : digit B (d 0 + B * ∑ m ∈ range n, d (m + 1) * B ^ m) (k + 1)
          = digit B (∑ m ∈ range n, d (m + 1) * B ^ m) k := by
        unfold digit
        rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt hd0, zero_add]
      rw [this]
      exact ih (fun m => d (m + 1)) (fun m hm => hd (m + 1) (by omega)) k (by omega)

theorem sq_pack (B N : ℕ) (a : ℕ → ℕ) :
    (∑ i ∈ range N, a i * B ^ i) * (∑ i ∈ range N, a i * B ^ i)
      = ∑ m ∈ range (2 * N), conv N a m * B ^ m := by
  rw [Finset.sum_mul_sum]
  have h1 : ∀ i ∈ range N, ∀ j ∈ range N, a i * B ^ i * (a j * B ^ j)
      = ∑ m ∈ range (2 * N), if i + j = m then a i * a j * B ^ m else 0 := by
    intro i hi j hj
    rw [Finset.sum_ite_eq]
    rw [if_pos (by simp at hi hj ⊢; omega), pow_add]; ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm, conv, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> first | omega | ring

theorem conv_le (N : ℕ) (a : ℕ → ℕ) (amax : ℕ) (ha : ∀ i < N, a i ≤ amax) (m : ℕ) :
    conv N a m ≤ N * amax ^ 2 := by
  unfold conv
  calc ∑ i ∈ range N, ∑ j ∈ range N, (if i + j = m then a i * a j else 0)
      ≤ ∑ i ∈ range N, amax ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc ∑ j ∈ range N, (if i + j = m then a i * a j else 0)
            ≤ ∑ j ∈ range N, (if j = m - i then a i * a j else 0) := by
              apply Finset.sum_le_sum; intro j _
              split_ifs with h1 h2 <;> first | exact le_rfl | omega
          _ = if m - i ∈ range N then a i * a (m - i) else 0 := Finset.sum_ite_eq' _ _ _
          _ ≤ amax ^ 2 := by
              split_ifs with h
              · simp at hi h
                rw [sq]; exact Nat.mul_le_mul (ha i hi) (ha _ h)
              · exact Nat.zero_le _
    _ = N * amax ^ 2 := by simp

/-- Main Kronecker certificate: digit checks on `A` and `A * A` bound every autoconvolution
value of the digit vector of `A`. -/
theorem kron_cert (B N amax M fuel1 fuel2 A : ℕ) (hA : A < B ^ N)
    (hamax : chk B amax fuel1 A N = true) (hB : N * amax ^ 2 < B)
    (hM : chk B M fuel2 (A * A) (2 * N) = true) :
    ∀ m < 2 * N, conv N (digit B A) m ≤ M := by
  intro m hm
  have ha : ∀ i < N, digit B A i ≤ amax := chk_sound B amax fuel1 A N hamax
  have hpack : ∑ i ∈ range N, digit B A i * B ^ i = A := by
    rw [sum_digit_pow, Nat.mod_eq_of_lt hA]
  have hsq := sq_pack B N (digit B A)
  rw [hpack] at hsq
  have hlt : ∀ m < 2 * N, conv N (digit B A) m < B :=
    fun m _ => lt_of_le_of_lt (conv_le N _ amax ha m) hB
  have hdig := digit_of_sum B (2 * N) (conv N (digit B A)) hlt m hm
  rw [← hsq] at hdig
  rw [← hdig]
  exact chk_sound B M fuel2 (A * A) (2 * N) hM m hm

end C1aUpper
