import C1aUpper.Kron

/-! Guard-bit certificates for packed natural numbers. The geometric mask is
computed by one power and quotient, independently of the number of fields. -/

namespace C1aUpper

open Finset

def unitMask (B n : ℕ) : ℕ := (B ^ n - 1) / (B - 1)

theorem unitMask_eq_sum {B n : ℕ} (hB : 2 ≤ B) :
    unitMask B n = ∑ j ∈ range n, B ^ j := (Nat.geomSum_eq hB n).symm

theorem digit_and (b X Y i : ℕ) :
    digit (2 ^ b) (X &&& Y) i = digit (2 ^ b) X i &&& digit (2 ^ b) Y i := by
  unfold digit
  rw [← pow_mul, Nat.and_div_two_pow, Nat.and_mod_two_pow]

theorem digit_repeated {B n T i : ℕ} (hB : 2 ≤ B) (hT : T < B) (hi : i < n) :
    digit B (T * unitMask B n) i = T := by
  rw [unitMask_eq_sum hB, Finset.mul_sum]
  exact digit_of_sum B n (fun _ => T) (fun _ _ => hT) i hi

/-- A repeated low-bit mask selecting all of Y bounds every input field. -/
theorem lowMask_sound {b w Y n : ℕ} (hb : 0 < b) (hw : w ≤ b)
    (hmask : Y &&& ((2 ^ w - 1) * unitMask (2 ^ b) n) = Y) :
    ∀ i < n, digit (2 ^ b) Y i < 2 ^ w := by
  intro i hi
  have hB : 2 ≤ 2 ^ b := Nat.one_lt_two_pow (by omega)
  have hpow : 2 ^ w ≤ (2 : ℕ) ^ b := Nat.pow_le_pow_right (by decide) hw
  have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have h := congrArg (fun Z => digit (2 ^ b) Z i) hmask
  change digit (2 ^ b) (Y &&& ((2 ^ w - 1) * unitMask (2 ^ b) n)) i = _ at h
  rw [digit_and, digit_repeated hB (by omega) hi] at h
  have hle : digit (2 ^ b) Y i ≤ 2 ^ w - 1 := by
    calc digit (2 ^ b) Y i = digit (2 ^ b) Y i &&& (2 ^ w - 1) := h.symm
      _ ≤ _ := Nat.and_le_right
  omega

/-- One guard bit per packed digit certifies an upper bound for every field. -/
theorem guard_pack_sound {k n Y M : ℕ} {d : ℕ → ℕ}
    (hpack : Y = ∑ i ∈ range n, d i * (2 ^ (k + 1)) ^ i)
    (hd : ∀ i < n, d i < 2 ^ k) (hM : M < 2 ^ k)
    (hguard : (Y + (2 ^ k - 1 - M) * unitMask (2 ^ (k+1)) n) &&&
      ((2 ^ k) * unitMask (2 ^ (k+1)) n) = 0) :
    ∀ i < n, d i ≤ M := by
  let L : ℕ := 2 ^ k
  let B : ℕ := 2 ^ (k+1)
  let pad : ℕ := L - 1 - M
  have hBL : B = L + L := by simp [B,L,pow_succ,Nat.mul_two]
  have hLM : M < L := hM
  have hB : 2 ≤ B := by omega
  have hpad (i) (hi : i < n) : d i + pad < B := by
    have h0 : d i < L := hd i hi
    dsimp [pad]
    omega
  have hsum : Y + pad * unitMask B n =
      ∑ i ∈ range n, (d i + pad) * B ^ i := by
    rw [hpack, unitMask_eq_sum hB, Finset.mul_sum]
    change (∑ i ∈ range n, d i * B ^ i) + _ = _
    simp only [Nat.add_mul, Finset.sum_add_distrib]
  intro i hi
  have h := congrArg (fun Z => digit B Z i) hguard
  change digit B ((Y + pad * unitMask B n) &&& (L * unitMask B n)) i = digit B 0 i at h
  rw [show digit B ((Y + pad * unitMask B n) &&& (L * unitMask B n)) i =
      digit B (Y + pad * unitMask B n) i &&& digit B (L * unitMask B n) i
      from digit_and (k+1) _ _ i, hsum, digit_of_sum B n (fun z => d z + pad) hpad i hi,
      digit_repeated hB (by omega) hi] at h
  simp only [digit, Nat.zero_div, Nat.zero_mod] at h
  by_contra! hbad
  have hhigh : 2 ^ k ≤ d i + pad := by
    change L ≤ _
    dsimp [pad]
    omega
  have hb := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hhigh (hpad i hi)
  have hz := congrArg (fun z : ℕ => z.testBit k) h
  change ((d i + pad) &&& (2 ^ k)).testBit k = (0 : ℕ).testBit k at hz
  simp [Nat.testBit_and, hb, Nat.testBit_two_pow_self] at hz

theorem guard_sound {k n Y M : ℕ}
    (hY : Y < (2 ^ (k+1)) ^ n)
    (hd : ∀ i < n, digit (2 ^ (k+1)) Y i < 2 ^ k) (hM : M < 2 ^ k)
    (hguard : (Y + (2 ^ k - 1 - M) * unitMask (2 ^ (k+1)) n) &&&
      ((2 ^ k) * unitMask (2 ^ (k+1)) n) = 0) :
    ∀ i < n, digit (2 ^ (k+1)) Y i ≤ M := by
  apply guard_pack_sound (Y := Y) _ hd hM hguard
  rw [sum_digit_pow, Nat.mod_eq_of_lt hY]

end C1aUpper

