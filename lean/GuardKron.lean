import Guard

namespace C1aUpper

open Finset

/-- Carry-free Kronecker substitution followed by a single guard-bit bound on
the convolution. The input and square may use different low-bit masks. -/
theorem kron_guard_cert {k w N A M : ℕ}
    (hw : w ≤ k + 1)
    (hA : A < (2 ^ (k+1)) ^ N)
    (hA_low : A &&& ((2 ^ w - 1) * unitMask (2 ^ (k+1)) N) = A)
    (hnoCarry : N * (2 ^ w - 1) ^ 2 < 2 ^ (k+1))
    (hY_low : (A * A) &&& ((2 ^ k - 1) * unitMask (2 ^ (k+1)) (2*N)) = A * A)
    (hM : M < 2 ^ k)
    (hguard : (A*A + (2 ^ k - 1 - M) * unitMask (2 ^ (k+1)) (2*N)) &&&
      (2 ^ k * unitMask (2 ^ (k+1)) (2*N)) = 0) :
    ∀ m < 2*N, conv N (digit (2 ^ (k+1)) A) m ≤ M := by
  let B : ℕ := 2 ^ (k+1)
  let a := digit B A
  have ha (i) (hi : i < N) : a i ≤ 2 ^ w - 1 := by
    have h := lowMask_sound (b := k+1) (w := w) (by omega) hw hA_low i hi
    change digit (2^(k+1)) A i ≤ _
    omega
  have hpack : ∑ i ∈ range N, a i * B ^ i = A := by
    change ∑ i ∈ range N, digit B A i * B ^ i = A
    rw [sum_digit_pow, Nat.mod_eq_of_lt hA]
  have hsq := sq_pack B N a
  rw [hpack] at hsq
  have hlt (m) (_hm : m < 2*N) : conv N a m < B :=
    lt_of_le_of_lt (conv_le N a (2 ^ w - 1) ha m) hnoCarry
  have hlow (m) (hm : m < 2*N) : conv N a m < 2 ^ k := by
    have hd := digit_of_sum B (2*N) (conv N a) hlt m hm
    rw [← hsq] at hd
    rw [← hd]
    exact lowMask_sound (b := k+1) (w := k) (by omega) (by omega) hY_low m hm
  exact guard_pack_sound (d := conv N a) hsq hlow hM hguard

end C1aUpper

#print axioms C1aUpper.kron_guard_cert

