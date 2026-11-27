import Guard
import C1aUpper.Data

namespace C1aUpper.Witness

theorem hA_low : A &&& ((2 ^ 79 - 1) * unitMask B N) = A := by decide +kernel

end C1aUpper.Witness
