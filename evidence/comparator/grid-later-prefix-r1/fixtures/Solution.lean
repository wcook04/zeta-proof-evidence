import LaterGridPrefix

open Enclosure ZetaGrid ZetaGridChecks LaterGridPrefix
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

theorem original_count : originalPrefix.length = 402 := by
  first | exact LaterGridPrefix.original_count | (apply LaterGridPrefix.original_count <;> assumption)

theorem moved_count : movedPrefix.length = 402 := by
  first | exact LaterGridPrefix.moved_count | (apply LaterGridPrefix.moved_count <;> assumption)

theorem original_classification : List.Forall Comparison.Check originalPrefix := by
  first | exact LaterGridPrefix.original_classification | (apply LaterGridPrefix.original_classification <;> assumption)

theorem original_reversed_sites :
    (originalPrefix.filter Comparison.reversed).map Comparison.site = [106, 114, 184, 242, 378] := by
  first | exact LaterGridPrefix.original_reversed_sites | (apply LaterGridPrefix.original_reversed_sites <;> assumption)

theorem moved_all_checks : List.Forall Comparison.Check movedPrefix := by
  first | exact LaterGridPrefix.moved_all_checks | (apply LaterGridPrefix.moved_all_checks <;> assumption)

theorem moved_all_forward : movedPrefix.all (fun row ↦ !row.reversed) = true := by
  first | exact LaterGridPrefix.moved_all_forward | (apply LaterGridPrefix.moved_all_forward <;> assumption)

end ZetaComparator
