import C1aUpper.Analytic
import C1aUpper.Data262144

/-!
# Upper bound on `C1a` from a 262144-step witness

The kernel checks the heights, their sum, and the autoconvolution certificate
for the witness packed in `C1aUpper.Data262144`.
-/

namespace C1aUpper

namespace D262144

open Finset

theorem hA : A < B ^ N := by decide +kernel
theorem hamax : chk B amax fuel A N = true := by decide +kernel
theorem hB : N * amax ^ 2 < B := by decide +kernel
theorem hM : chk B M fuel (A * A) (2 * N) = true := by decide +kernel
theorem hS : S ≤ dsum B fuel A N := by decide +kernel

theorem conv_bound : ∀ m < 2 * N, conv N (digit B A) m ≤ M :=
  kron_cert B N amax M fuel fuel A hA hamax hB hM

theorem sum_bound : S ≤ ∑ i ∈ range N, digit B A i :=
  le_trans hS (dsum_le B fuel A N)

end D262144

open D262144 in
/-- The exact upper bound certified by the 262144-step witness. -/
theorem c1a_upper_262144 :
    Constant1a.C1a ≤ (24440309691768679463247675392 : ℝ) / 16264647129627086646956500225 := by
  have h := C1a_le_of_steps N (by decide) (digit B A) M S (by decide) sum_bound conv_bound
  have e : (2 * (N : ℝ) * M) / (S : ℝ) ^ 2 =
      24440309691768679463247675392 / 16264647129627086646956500225 := by
    unfold N M S
    norm_num
  rwa [e] at h

/-- The witness also certifies this rounded decimal upper bound. -/
theorem c1a_upper_beats_pr408 : Constant1a.C1a ≤ (1.502664614 : ℝ) :=
  le_trans c1a_upper_262144 (by norm_num)

/-- The new upper bound is strictly below the exact bound in PR #408. -/
theorem c1a_upper_lt_pr408 :
    Constant1a.C1a < (30550410444162607556776689664 : ℝ) / 20330824246169453284105633005 :=
  lt_of_le_of_lt c1a_upper_beats_pr408 (by norm_num)

end C1aUpper
