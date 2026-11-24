import GridSourceBinding

open ZetaGrid ZetaGridChecks
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem pinned_row_count : (pinnedRows.map (fun part ↦ part.2.length)).sum = 10104 := by
  first | exact ZetaGridChecks.pinned_row_count | (apply ZetaGridChecks.pinned_row_count <;> assumption)

theorem pinnedRows_recover_sharedBatches :
    pinnedRows.map (fun part ↦ sourceComparisons part.1 part.2) = sharedBatches := by
  first | exact ZetaGridChecks.pinnedRows_recover_sharedBatches | (apply ZetaGridChecks.pinnedRows_recover_sharedBatches <;> assumption)

theorem pinned_shared_checked (row : Comparison)
    (h : row ∈ (pinnedRows.map (fun p ↦ sourceComparisons p.1 p.2)).flatten) :
    row.Check := by
  first | exact ZetaGridChecks.pinned_shared_checked | (apply ZetaGridChecks.pinned_shared_checked <;> assumption)

theorem pinned_own_checked (row : Comparison)
    (h : row ∈ (pinnedRows.map (fun p ↦ originalOwnComparisons p.1 p.2)).flatten) :
    row.Check := by
  first | exact ZetaGridChecks.pinned_own_checked | (apply ZetaGridChecks.pinned_own_checked <;> assumption)

theorem shared_checked (row : Comparison) (h : row ∈ sharedBatches.flatten) : row.Check := by
  first | exact ZetaGridChecks.shared_checked | (apply ZetaGridChecks.shared_checked <;> assumption)

theorem shared_check_count : sharedBatches.flatten.length = 10155 := by
  first | exact ZetaGridChecks.shared_check_count | (apply ZetaGridChecks.shared_check_count <;> assumption)

theorem shared_batched_checks : List.Forall (List.Forall Comparison.Check) sharedBatches := by
  first | exact ZetaGridChecks.shared_batched_checks | (apply ZetaGridChecks.shared_batched_checks <;> assumption)

end ZetaComparator
