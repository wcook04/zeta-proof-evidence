import GridMargins
import MovedSigns
import RSZeroCoefficient
import RSGridOptimality

open Enclosure ZetaGrid ZetaGridChecks ZetaGridPlacement Zeta.RiemannSiegel
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem moved_shared_106 :
    error (sfrac false 1 8) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 247551 1000) := by
  sorry

theorem original_shared_failure_106 :
    (-1) * hardyZApproximantRS₀ (sfrac false 247179 1000) <
      error (sfrac false 1 8) (sfrac false 149500 1000) := by
  sorry

theorem moved_legacy_106 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 247551 1000) := by
  sorry

theorem original_own_106 :
    error (sfrac false 1 8) (sfrac false 247179 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 247179 1000) := by
  sorry

theorem moved_shared_114 :
    error (sfrac false 1 8) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 260396 1000) := by
  sorry

theorem original_shared_failure_114 :
    (-1) * hardyZApproximantRS₀ (sfrac false 260767 1000) <
      error (sfrac false 1 8) (sfrac false 149500 1000) := by
  sorry

theorem moved_legacy_114 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 260396 1000) := by
  sorry

theorem original_own_114 :
    error (sfrac false 1 8) (sfrac false 260767 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 260767 1000) := by
  sorry

theorem moved_shared_184 :
    error (sfrac false 1 8) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 373431 1000) := by
  sorry

theorem original_shared_failure_184 :
    (-1) * hardyZApproximantRS₀ (sfrac false 373095 1000) <
      error (sfrac false 1 8) (sfrac false 149500 1000) := by
  sorry

theorem moved_legacy_184 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 373431 1000) := by
  sorry

theorem original_own_184 :
    error (sfrac false 1 8) (sfrac false 373095 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 373095 1000) := by
  sorry

theorem moved_shared_242 :
    error (sfrac false 1 8) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 459791 1000) := by
  sorry

theorem original_shared_failure_242 :
    (-1) * hardyZApproximantRS₀ (sfrac false 460021 1000) <
      error (sfrac false 1 8) (sfrac false 149500 1000) := by
  sorry

theorem moved_legacy_242 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 459791 1000) := by
  sorry

theorem original_own_242 :
    error (sfrac false 1 8) (sfrac false 460021 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 460021 1000) := by
  sorry

theorem moved_shared_378 :
    error (sfrac false 1 8) (sfrac false 474603 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 650467 1000) := by
  sorry

theorem original_shared_failure_378 :
    (-1) * hardyZApproximantRS₀ (sfrac false 650214 1000) <
      error (sfrac false 1 8) (sfrac false 474603 1000) := by
  sorry

theorem moved_legacy_378 :
    error (sfrac false 13 10) (sfrac false 474603 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 650467 1000) := by
  sorry

theorem original_own_378 :
    error (sfrac false 1 8) (sfrac false 650214 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 650214 1000) := by
  sorry

theorem moved_own_3823 :
    error (sfrac false 1 5) (sfrac false 4337288 1000) <
      1 * hardyZApproximantRS₀ (sfrac false 4337288 1000) := by
  sorry

theorem original_own_failure_3823 :
    1 * hardyZApproximantRS₀ (sfrac false 4337135 1000) <
      error (sfrac false 1 5) (sfrac false 4337135 1000) := by
  sorry

theorem runner_up_pass_4765 :
    error (sfrac false 1 5) (sfrac false 5229207 1000) <
      1 * hardyZApproximantRS₀ (sfrac false 5229207 1000) := by
  sorry

theorem runner_up_fail_4765 :
    1 * hardyZApproximantRS₀ (sfrac false 5229207 1000) <
      error (sfrac false 247 1000) (sfrac false 5229207 1000) := by
  sorry

theorem moved_count : moved_inputs.length = 24 := by
  sorry

theorem moved_checks : List.Forall Comparison.Check moved_inputs := by
  sorry

theorem moved_checked (row : Comparison) (h : row ∈ moved_inputs) : row.Check := by
  sorry

theorem hardyZ_moved_106 : Zeta.hardyZ (sfrac false 247551 1000) < 0 := by
  sorry

theorem hardyZ_moved_114 : Zeta.hardyZ (sfrac false 260396 1000) < 0 := by
  sorry

theorem hardyZ_moved_184 : Zeta.hardyZ (sfrac false 373431 1000) < 0 := by
  sorry

theorem hardyZ_moved_242 : Zeta.hardyZ (sfrac false 459791 1000) < 0 := by
  sorry

theorem hardyZ_moved_378 : Zeta.hardyZ (sfrac false 650467 1000) < 0 := by
  sorry

theorem all_moved_negative (row : ℕ × ℕ × ℕ) (h : row ∈ movedHeights) :
    Zeta.hardyZ (sfrac false row.2.1 row.2.2) < 0 := by
  sorry

theorem hardyZ_left_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 245466 1000) := by
  sorry

theorem hardyZ_right_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 248888 1000) := by
  sorry

theorem hardyZ_left_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 259079 1000) := by
  sorry

theorem hardyZ_right_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 262452 1000) := by
  sorry

theorem hardyZ_left_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 371556 1000) := by
  sorry

theorem hardyZ_right_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 374633 1000) := by
  sorry

theorem hardyZ_left_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 458557 1000) := by
  sorry

theorem hardyZ_right_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 461484 1000) := by
  sorry

theorem hardyZ_left_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 649537 1000) := by
  sorry

theorem hardyZ_right_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 652244 1000) := by
  sorry

theorem fiveForcedSites_card : fiveForcedSites.card = 5 := by
  sorry

theorem original_forcedSite_fails (i : ℕ) (hi : i ∈ fiveForcedSites) :
    ¬ forcedSitePass i (originalForcedHeight i) := by
  sorry

theorem replacement_forcedSite_passes (i : ℕ) (hi : i ∈ fiveForcedSites) :
    forcedSitePass i (replacementForcedHeight i) := by
  sorry

theorem five_forcedSites_must_move {grid : ℕ → ℝ} {moves : Finset ℕ}
    (hfixed : ∀ i ∈ fiveForcedSites, i ∉ moves → grid i = originalForcedHeight i)
    (hpass : ∀ i ∈ fiveForcedSites, forcedSitePass i (grid i)) :
    fiveForcedSites ⊆ moves := by
  sorry

theorem five_le_card_moves_of_fixed_shared_pass {grid : ℕ → ℝ} {moves : Finset ℕ}
    (hfixed : ∀ i ∈ fiveForcedSites, i ∉ moves → grid i = originalForcedHeight i)
    (hpass : ∀ i ∈ fiveForcedSites, forcedSitePass i (grid i)) :
    5 ≤ moves.card := by
  sorry

theorem original_forcedSite_passes_own (i : ℕ) (hi : i ∈ fiveForcedSites) :
    error (sfrac false 1 8) (originalForcedHeight i) <
      (-1) * hardyZApproximantRS₀ (originalForcedHeight i) := by
  sorry

theorem hardyZ_original_forcedSites_neg
    (hC : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → |correctionLinear p| ≤ (1 / 8 : ℝ))
    (i : ℕ) (hi : i ∈ fiveForcedSites) :
    Zeta.hardyZ (originalForcedHeight i) < 0 := by
  sorry

theorem hardyZ_replacement_forcedSites_neg
    (hC : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → |correctionLinear p| ≤ (1 / 8 : ℝ))
    (i : ℕ) (hi : i ∈ fiveForcedSites) :
    Zeta.hardyZ (replacementForcedHeight i) < 0 := by
  sorry

theorem fiveForcedSites_hardyZ_neg (i : ℕ) (hi : i ∈ fiveForcedSites) :
    Zeta.hardyZ (originalForcedHeight i) < 0 ∧
      Zeta.hardyZ (replacementForcedHeight i) < 0 := by
  sorry

theorem ownHeight_oneMove_optimal_of_separators {ι : Type*}
    {σ original replacement : ι → ℝ} {limiting runnerUp : ι} {low high : ℝ}
    (hneq : limiting ≠ runnerUp)
    (hOrigPos : ∀ i, 0 < original i) (hNewPos : ∀ i, 0 < replacement i)
    (hlim : ownHeightStrictFailure low (σ limiting) (original limiting))
    (hlo : ownHeightPass low (σ runnerUp) (original runnerUp))
    (hhi : ownHeightStrictFailure high (σ runnerUp) (original runnerUp))
    (hrest : ∀ i, i ≠ limiting → i ≠ runnerUp →
      ownHeightPass high (σ i) (original i))
    (hmoved : ownHeightPass high (σ limiting) (replacement limiting))
    (hfixed : ∀ i, i ≠ limiting → replacement i = original i) :
    let initialThreshold := coefficientThresholdRS₀ (original limiting) (original limiting) (σ limiting)
    let improvedThreshold := coefficientThresholdRS₀ (original runnerUp) (original runnerUp) (σ runnerUp)
    (∀ c, (∀ i, ownHeightPass c (σ i) (original i)) ↔ c < initialThreshold) ∧
    (∀ c, (∀ i, ownHeightPass c (σ i) (replacement i)) ↔ c < improvedThreshold) ∧
    (∀ (c : ℝ) (site : ι) (alternative : ι → ℝ),
      (∀ i, 0 < alternative i) →
      (∀ i, i ≠ site → alternative i = original i) →
      (∀ i, ownHeightPass c (σ i) (alternative i)) →
      c < improvedThreshold) := by
  sorry

theorem threeForcedSites_card : threeForcedSites.card = 3 := by
  sorry

theorem original_shared_strictFailure_at_any_nonneg_coefficient
    (c : ℝ) (hc : 0 ≤ c) (i : ℕ) (hi : i ∈ threeForcedSites) :
    (-1) * hardyZApproximantRS₀ (originalForcedHeight i) <
      error c (forcedSiteBatchLow i) := by
  sorry

theorem three_forcedSites_must_move_for_any_nonnegative_coefficient
    {c : ℝ} (hc : 0 ≤ c) {grid : ℕ → ℝ} {moves : Finset ℕ}
    (hfixed : ∀ i ∈ threeForcedSites, i ∉ moves → grid i = originalForcedHeight i)
    (hpass : ∀ i ∈ threeForcedSites,
      error c (forcedSiteBatchLow i) < (-1) * hardyZApproximantRS₀ (grid i)) :
    threeForcedSites ⊆ moves := by
  sorry

theorem three_le_card_moves_for_any_nonnegative_coefficient
    {c : ℝ} (hc : 0 ≤ c) {grid : ℕ → ℝ} {moves : Finset ℕ}
    (hfixed : ∀ i ∈ threeForcedSites, i ∉ moves → grid i = originalForcedHeight i)
    (hpass : ∀ i ∈ threeForcedSites,
      error c (forcedSiteBatchLow i) < (-1) * hardyZApproximantRS₀ (grid i)) :
    3 ≤ moves.card := by
  sorry

end ZetaComparator
