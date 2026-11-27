import C1aUpper.Data

namespace C1aUpper.Witness

theorem hA : A < B ^ N := by decide +kernel
theorem hB : N * amax ^ 2 < B := by decide +kernel

end C1aUpper.Witness
