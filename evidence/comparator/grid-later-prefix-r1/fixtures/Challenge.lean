import LaterGridPrefix

open Enclosure ZetaGrid ZetaGridChecks LaterGridPrefix
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem original_count : originalPrefix.length = 402 := by
  sorry

theorem moved_count : movedPrefix.length = 402 := by
  sorry

theorem original_classification : List.Forall Comparison.Check originalPrefix := by
  sorry

theorem original_reversed_sites :
    (originalPrefix.filter Comparison.reversed).map Comparison.site = [106, 114, 184, 242, 378] := by
  sorry

theorem moved_all_checks : List.Forall Comparison.Check movedPrefix := by
  sorry

theorem moved_all_forward : movedPrefix.all (fun row ↦ !row.reversed) = true := by
  sorry

end ZetaComparator
