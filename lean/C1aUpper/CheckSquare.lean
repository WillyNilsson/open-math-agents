import Guard
import C1aUpper.Data

namespace C1aUpper.Witness

theorem hY_low : (A * A) &&& ((2 ^ 176 - 1) * unitMask B (2 * N)) = A * A := by decide +kernel

end C1aUpper.Witness
