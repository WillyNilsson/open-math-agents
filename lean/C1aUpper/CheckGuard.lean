import Guard
import C1aUpper.Data

namespace C1aUpper.Witness

theorem hguard : ((A * A) + (2 ^ 176 - 1 - M) * unitMask B (2 * N)) &&& ((2 ^ 176) * unitMask B (2 * N)) = 0 := by decide +kernel

end C1aUpper.Witness
