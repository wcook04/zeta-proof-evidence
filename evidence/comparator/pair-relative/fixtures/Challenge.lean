module

public import RelativeComponentProof

@[expose] public section

namespace ZetaComparatorComponents

open Complex ZetaFiniteHeight ZetaLogRobustness ZetaMercuriXi

open scoped BigOperators

theorem component_logWeight_norm : (∑ i, |logWeight i|) = (22654336 / 3375 : ℝ) := by
  sorry

theorem component_upper_perturb_logs (x y z : ℝ) (e : Fin 7 → ℝ) :
    WideMoment.upper (x + (2 * e 0 - e 1 - e 2))
      (y + (2 * e 0 - e 3 - e 4)) (z + (2 * e 0 - e 5 - e 6)) =
        WideMoment.upper x y z + weightedLogDelta e := by
  sorry

theorem component_weightedLogDelta_abs_le {e : Fin 7 → ℝ} {δ : ℝ}
    (he : ∀ i, |e i| ≤ δ) :
    |weightedLogDelta e| ≤ δ * (22654336 / 3375) := by
  sorry

theorem component_upper_perturb_logs_abs_le (x y z : ℝ) {e : Fin 7 → ℝ} {δ : ℝ}
    (he : ∀ i, |e i| ≤ δ) :
    |WideMoment.upper (x + (2 * e 0 - e 1 - e 2))
      (y + (2 * e 0 - e 3 - e 4)) (z + (2 * e 0 - e 5 - e 6)) -
      WideMoment.upper x y z| ≤ δ * (22654336 / 3375) := by
  sorry

theorem component_relative_transport_lt_robust :
    transport * (widenedObservation / (1 - 1 / 10 ^ 7)) < robustScoreCutoff := by
  sorry

theorem component_robustScoreCutoff_lt : robustScoreCutoff < (799995 / 10 ^ 6 : ℝ) := by
  sorry

end ZetaComparatorComponents

end
