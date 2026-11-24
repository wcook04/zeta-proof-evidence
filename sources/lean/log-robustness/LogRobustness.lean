module

public import MercuriXiNamedProof
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Robustness of the named seven-probe certificate under independent log errors. -/

namespace ZetaLogRobustness

open scoped BigOperators
open ZetaMercuriXi ZetaFiniteHeight

noncomputable section

abbrev w₁ : ℝ := 4781472 / 4025
abbrev w₂ : ℝ := 863744 / 675
abbrev w₃ : ℝ := 266338304 / 543375

/-- Midpoint first, then the two points at each of the three radii in order. -/
def logWeight : Fin 7 → ℝ :=
  ![2 * (w₁ - w₂ + w₃), -w₁, -w₁, w₂, w₂, -w₃, -w₃]

def weightedLogDelta (e : Fin 7 → ℝ) : ℝ := ∑ i, logWeight i * e i

theorem logWeight_norm : (∑ i, |logWeight i|) = (22654336 / 3375 : ℝ) := by
  norm_num [logWeight, Fin.sum_univ_succ, w₁, w₂, w₃]

/-- Root corrections stay fixed when only the seven log entries are changed. -/
theorem upper_perturb_logs (x y z : ℝ) (e : Fin 7 → ℝ) :
    WideMoment.upper (x + (2 * e 0 - e 1 - e 2))
      (y + (2 * e 0 - e 3 - e 4)) (z + (2 * e 0 - e 5 - e 6)) =
        WideMoment.upper x y z + weightedLogDelta e := by
  norm_num [WideMoment.upper, weightedLogDelta, logWeight, Fin.sum_univ_succ,
    w₁, w₂, w₃]
  ring

theorem weightedLogDelta_abs_le {e : Fin 7 → ℝ} {δ : ℝ}
    (he : ∀ i, |e i| ≤ δ) :
    |weightedLogDelta e| ≤ δ * (22654336 / 3375) := by
  unfold weightedLogDelta
  calc
    |∑ i, logWeight i * e i| ≤ ∑ i, |logWeight i * e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |logWeight i| * |e i| := by simp only [abs_mul]
    _ ≤ ∑ i, |logWeight i| * δ :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (he i) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, logWeight_norm, mul_comm]

/-- The change of the upper stencil when the seven scalar logs move separately. -/
theorem upper_perturb_logs_abs_le (x y z : ℝ) {e : Fin 7 → ℝ} {δ : ℝ}
    (he : ∀ i, |e i| ≤ δ) :
    |WideMoment.upper (x + (2 * e 0 - e 1 - e 2))
      (y + (2 * e 0 - e 3 - e 4)) (z + (2 * e 0 - e 5 - e 6)) -
      WideMoment.upper x y z| ≤ δ * (22654336 / 3375) := by
  rw [upper_perturb_logs, add_sub_cancel_left]
  exact weightedLogDelta_abs_le he

abbrev logRadius : ℝ := 3 / 10 ^ 9

def widenedObservation : ℝ := 7999747 / 10000000 + logRadius * (22654336 / 3375)

abbrev robustScoreCutoff : ℝ := 799994918214 / 10 ^ 12

theorem relative_transport_lt_robust :
    transport * (widenedObservation / (1 - 1 / 10 ^ 7)) < robustScoreCutoff := by
  norm_num [transport, WideMoment.transportFactor, halfGap, rootRadius,
    widenedObservation, logRadius, robustScoreCutoff]

theorem robustScoreCutoff_lt : robustScoreCutoff < (799995 / 10 ^ 6 : ℝ) := by
  norm_num [robustScoreCutoff]

/-- The named proof supplies the root boxes, rank, and sharp observation.
No sample needs to be evaluated again to enlarge the interval. -/
theorem originalPair2391_2392_robust :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b robustScoreCutoff ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ logRadius) →
        pairObservation a b + weightedLogDelta e ≤ widenedObservation := by
  obtain ⟨a, b, ha, hb, roots, _⟩ := originalPair2391_2392_strict
  have hsharp := pairObservation_le_sharp roots ha hb
  have hobs : pairObservation a b ≤ widenedObservation :=
    hsharp.trans (by norm_num [widenedObservation, logRadius])
  have hscore := pair2391_of_actualXi_cutoff roots
    (atlas_line_upto ZetaSourceRows.originalAtlas ZetaSourceRows.originalCount_height_ge_10000)
    hobs relative_transport_lt_robust
  refine ⟨a, b, ha, hb, roots, hscore, fun e he ↦ ?_⟩
  exact add_le_add hsharp ((le_abs_self _).trans (weightedLogDelta_abs_le he))

#print axioms logWeight_norm
#print axioms upper_perturb_logs
#print axioms weightedLogDelta_abs_le
#print axioms upper_perturb_logs_abs_le
#print axioms relative_transport_lt_robust
#print axioms robustScoreCutoff_lt
#print axioms originalPair2391_2392_robust

end
end ZetaLogRobustness

end
