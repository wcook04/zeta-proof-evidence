import C1Bound
import C1DecimalBound

open Zeta.RiemannSiegel
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem abs_correctionLinear_lt_eighth {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |correctionLinear p| < 1 / 8 := by
  first | exact Zeta.RiemannSiegel.abs_correctionLinear_lt_eighth | (apply Zeta.RiemannSiegel.abs_correctionLinear_lt_eighth <;> assumption)

theorem abs_correctionLinear_lt_decimal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |correctionLinear p| < (122459896 : ℝ) / 1000000000 := by
  first | exact Zeta.RiemannSiegel.abs_correctionLinear_lt_decimal | (apply Zeta.RiemannSiegel.abs_correctionLinear_lt_decimal <;> assumption)

end ZetaComparator
