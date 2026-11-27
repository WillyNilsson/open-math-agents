import C1aUpper.Analytic
import GuardKron
import C1aUpper.CheckSize
import C1aUpper.CheckHeights
import C1aUpper.CheckSum
import C1aUpper.CheckSquare
import C1aUpper.CheckGuard

/-!
# Upper bound on `C1a` from a 524288-step witness

The kernel checks the heights, their sum, and the autoconvolution certificate
for the witness packed in `C1aUpper.Data`.
-/

namespace C1aUpper


/-- Use an explicit radix throughout to avoid reducing a large concrete packed
power merely to unify two ways of writing the small radix exponent. -/
theorem guarded_conv_with_radix {B k w N A M : ℕ}
    (hbase : B = 2 ^ (k + 1)) (hw : w ≤ k + 1)
    (hA : A < B ^ N)
    (hA_low : A &&& ((2 ^ w - 1) * unitMask B N) = A)
    (hnoCarry : N * (2 ^ w - 1) ^ 2 < B)
    (hY_low : (A * A) &&& ((2 ^ k - 1) * unitMask B (2 * N)) = A * A)
    (hM : M < 2 ^ k)
    (hguard : ((A * A) + (2 ^ k - 1 - M) * unitMask B (2 * N)) &&&
      ((2 ^ k) * unitMask B (2 * N)) = 0) :
    ∀ m < 2 * N, conv N (digit B A) m ≤ M := by
  subst B
  exact kron_guard_cert hw hA hA_low hnoCarry hY_low hM hguard

namespace Witness

open Finset


theorem conv_bound : ∀ m < 2 * N, conv N (digit B A) m ≤ M :=
  guarded_conv_with_radix (B := B) (k := 176) (w := 79) (N := N) (A := A) (M := M) (by decide +kernel) (by decide +kernel) hA hA_low (by decide +kernel) hY_low (by decide +kernel) hguard

theorem sum_bound : S ≤ ∑ i ∈ range N, digit B A i :=
  hS

end Witness

open Witness in
/-- The exact upper bound certified by the 524288-step witness. -/
theorem c1a_upper_verified :
    Constant1a.C1a ≤ (519430314903936621654612615023564348717838184096989184 : ℝ) / 345672820315193691904670643895864696282762768089237289 := by
  have h := C1a_le_of_steps N (by decide) (digit B A) M S (by decide) sum_bound conv_bound
  have e : (2 * (N : ℝ) * M) / (S : ℝ) ^ 2 =
      519430314903936621654612615023564348717838184096989184 / 345672820315193691904670643895864696282762768089237289 := by
    unfold N M S
    norm_num
  rwa [e] at h

end C1aUpper
