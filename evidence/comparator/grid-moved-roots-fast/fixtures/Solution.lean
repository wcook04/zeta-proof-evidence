module

public import ActualMoves

open Set ZetaSourceRows Zeta.Certificates Enclosure ZetaGridChecks
open scoped Nat Real

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace ZetaComparator

public theorem actual_five_replacements_preserve_indexed_roots {r : GridReplacement}
    (hr : r ∈ fiveReplacements) :
    originalAtlas.root (leftMoveIndex r hr) ∈ Ioo r.lower r.moved ∧
      originalAtlas.root (rightMoveIndex r hr) ∈ Ioo r.moved r.upper := by
  first | exact ZetaSourceRows.actual_five_replacements_preserve_indexed_roots | (apply ZetaSourceRows.actual_five_replacements_preserve_indexed_roots <;> assumption)

public theorem fiveReplacements_trueSigns {r : GridReplacement} (hr : r ∈ fiveReplacements) :
    0 < Zeta.hardyZ r.lower ∧ Zeta.hardyZ r.moved < 0 ∧ 0 < Zeta.hardyZ r.upper := by
  first | exact ZetaSourceRows.fiveReplacements_trueSigns | (apply ZetaSourceRows.fiveReplacements_trueSigns <;> assumption)

public theorem independent_assembly_same_root : movesAtlas.root = originalAtlas.root := by
  first | exact ZetaSourceRows.independent_assembly_same_root | (apply ZetaSourceRows.independent_assembly_same_root <;> assumption)

public theorem hardyZ_moved_106 : Zeta.hardyZ (sfrac false 247551 1000) < 0 := by
  first | exact ZetaGridChecks.hardyZ_moved_106 | (apply ZetaGridChecks.hardyZ_moved_106 <;> assumption)

public theorem hardyZ_left_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 245466 1000) := by
  first | exact ZetaGridChecks.hardyZ_left_neighbor_106 | (apply ZetaGridChecks.hardyZ_left_neighbor_106 <;> assumption)

public theorem hardyZ_right_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 248888 1000) := by
  first | exact ZetaGridChecks.hardyZ_right_neighbor_106 | (apply ZetaGridChecks.hardyZ_right_neighbor_106 <;> assumption)

public theorem hardyZ_moved_114 : Zeta.hardyZ (sfrac false 260396 1000) < 0 := by
  first | exact ZetaGridChecks.hardyZ_moved_114 | (apply ZetaGridChecks.hardyZ_moved_114 <;> assumption)

public theorem hardyZ_left_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 259079 1000) := by
  first | exact ZetaGridChecks.hardyZ_left_neighbor_114 | (apply ZetaGridChecks.hardyZ_left_neighbor_114 <;> assumption)

public theorem hardyZ_right_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 262452 1000) := by
  first | exact ZetaGridChecks.hardyZ_right_neighbor_114 | (apply ZetaGridChecks.hardyZ_right_neighbor_114 <;> assumption)

public theorem hardyZ_moved_184 : Zeta.hardyZ (sfrac false 373431 1000) < 0 := by
  first | exact ZetaGridChecks.hardyZ_moved_184 | (apply ZetaGridChecks.hardyZ_moved_184 <;> assumption)

public theorem hardyZ_left_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 371556 1000) := by
  first | exact ZetaGridChecks.hardyZ_left_neighbor_184 | (apply ZetaGridChecks.hardyZ_left_neighbor_184 <;> assumption)

public theorem hardyZ_right_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 374633 1000) := by
  first | exact ZetaGridChecks.hardyZ_right_neighbor_184 | (apply ZetaGridChecks.hardyZ_right_neighbor_184 <;> assumption)

public theorem hardyZ_moved_242 : Zeta.hardyZ (sfrac false 459791 1000) < 0 := by
  first | exact ZetaGridChecks.hardyZ_moved_242 | (apply ZetaGridChecks.hardyZ_moved_242 <;> assumption)

public theorem hardyZ_left_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 458557 1000) := by
  first | exact ZetaGridChecks.hardyZ_left_neighbor_242 | (apply ZetaGridChecks.hardyZ_left_neighbor_242 <;> assumption)

public theorem hardyZ_right_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 461484 1000) := by
  first | exact ZetaGridChecks.hardyZ_right_neighbor_242 | (apply ZetaGridChecks.hardyZ_right_neighbor_242 <;> assumption)

public theorem hardyZ_moved_378 : Zeta.hardyZ (sfrac false 650467 1000) < 0 := by
  first | exact ZetaGridChecks.hardyZ_moved_378 | (apply ZetaGridChecks.hardyZ_moved_378 <;> assumption)

public theorem hardyZ_left_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 649537 1000) := by
  first | exact ZetaGridChecks.hardyZ_left_neighbor_378 | (apply ZetaGridChecks.hardyZ_left_neighbor_378 <;> assumption)

public theorem hardyZ_right_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 652244 1000) := by
  first | exact ZetaGridChecks.hardyZ_right_neighbor_378 | (apply ZetaGridChecks.hardyZ_right_neighbor_378 <;> assumption)

end ZetaComparator
