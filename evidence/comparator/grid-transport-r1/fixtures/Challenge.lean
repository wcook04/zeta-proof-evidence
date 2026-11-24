import RSTransportCore

open Zeta.RiemannSiegel
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem abs_correctionLinear_le_of_third_deriv {c p : ℝ}
    (h : |iteratedDeriv 3 correction p| ≤ 96 * Real.pi ^ 2 * c) :
    |correctionLinear p| ≤ c := by
  sorry

theorem abs_hardyZRemainderRS₀_le_with {c t : ℝ}
    (hC : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → |correctionLinear p| ≤ c)
    (ht : 16 ≤ t / (2 * Real.pi)) :
    |hardyZRemainderRS₀ t| ≤ hardyZErrorBoundRS₀With c t := by
  sorry

theorem hardyZSign_of_own_signedMargin {c t σ : ℝ}
    (hC : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → |correctionLinear p| ≤ c)
    (ht : 16 ≤ t / (2 * Real.pi)) (hσ : σ = 1 ∨ σ = -1)
    (hm : hardyZErrorBoundRS₀With c t < σ * hardyZApproximantRS₀ t) :
    0 < σ * Zeta.hardyZ t := by
  sorry

theorem hardyZSign_of_signedMargin {c s t σ : ℝ}
    (hC : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → |correctionLinear p| ≤ c)
    (hs : 0 < s) (hst : s ≤ t) (ht : 16 ≤ t / (2 * Real.pi))
    (hσ : σ = 1 ∨ σ = -1)
    (hm : hardyZErrorBoundRS₀With c s < σ * hardyZApproximantRS₀ t) :
    0 < σ * Zeta.hardyZ t := by
  sorry

theorem abs_hardyZRemainderRS₀_le_eighth {t : ℝ} (ht : 16 ≤ t / (2 * Real.pi)) :
    |hardyZRemainderRS₀ t| ≤ hardyZErrorBoundRS₀With (1 / 8) t := by
  sorry

end ZetaComparator
