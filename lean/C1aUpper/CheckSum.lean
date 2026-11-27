import C1aUpper.CheckSize

namespace C1aUpper

open Finset

theorem packed_mod_le_digit_sum (B A N : ℕ) (hB : 1 < B) (hA : A < B ^ N) :
    A % (B - 1) ≤ ∑ i ∈ range N, digit B A i := by
  have hb : B ≡ 1 [MOD B - 1] :=
    ((Nat.modEq_iff_dvd' hB.le).2 (dvd_refl (B - 1))).symm
  have hs : (∑ i ∈ range N, digit B A i * B ^ i) ≡
      (∑ i ∈ range N, digit B A i) [MOD B - 1] := by
    apply Nat.ModEq.sum
    intro i _
    simpa using (hb.pow i).mul_left (digit B A i)
  rw [sum_digit_pow, Nat.mod_eq_of_lt hA] at hs
  exact le_trans hs.le (Nat.mod_le _ _)

end C1aUpper

namespace C1aUpper.Witness
open Finset
theorem hS : S ≤ ∑ i ∈ range N, digit B A i := by
  have hchecksum : S = A % (B - 1) := by decide +kernel
  rw [hchecksum]
  exact packed_mod_le_digit_sum B A N (by decide +kernel) hA
end C1aUpper.Witness
