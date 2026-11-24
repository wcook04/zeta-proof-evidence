import generated.shared.GridBatch001
import generated.shared.GridBatch002
import generated.shared.GridBatch003
import generated.shared.GridBatch004
import generated.shared.GridBatch005
import generated.shared.GridBatch006
import generated.shared.GridBatch007
import generated.shared.GridBatch008
import generated.shared.GridBatch009
import generated.shared.GridBatch010
import generated.shared.GridBatch011
import generated.shared.GridBatch012
import generated.shared.GridBatch013
import generated.shared.GridBatch014
import generated.shared.GridBatch015
import generated.shared.GridBatch016
import generated.shared.GridBatch017
import generated.shared.GridBatch018
import generated.shared.GridBatch019
import generated.shared.GridBatch020
import generated.shared.GridBatch021
import generated.shared.GridBatch022
import generated.shared.GridBatch023
import generated.shared.GridBatch024
import generated.shared.GridBatch025
import generated.shared.GridBatch026
import generated.shared.GridBatch027
import generated.shared.GridBatch028
import generated.shared.GridBatch029
import generated.shared.GridBatch030
import generated.shared.GridBatch031
import generated.shared.GridBatch032
import generated.shared.GridBatch033
import generated.shared.GridBatch034
import generated.shared.GridBatch035
import generated.shared.GridBatch036
import generated.shared.GridBatch037
import generated.shared.GridBatch038
import generated.shared.GridBatch039
import generated.shared.GridBatch040
import generated.shared.GridBatch041
import generated.shared.GridBatch042
import generated.shared.GridBatch043
import generated.shared.GridBatch044
import generated.shared.GridBatch045
import generated.shared.GridBatch046
import generated.shared.GridBatch047
import generated.shared.GridBatch048
import generated.shared.GridBatch049
import generated.shared.GridBatch050
import generated.shared.GridBatch051

open Enclosure ZetaGrid

set_option maxRecDepth 100000
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ZetaGridChecks


def sharedBatches : List (List Comparison) := [
  batch_001_inputs,
  batch_002_inputs,
  batch_003_inputs,
  batch_004_inputs,
  batch_005_inputs,
  batch_006_inputs,
  batch_007_inputs,
  batch_008_inputs,
  batch_009_inputs,
  batch_010_inputs,
  batch_011_inputs,
  batch_012_inputs,
  batch_013_inputs,
  batch_014_inputs,
  batch_015_inputs,
  batch_016_inputs,
  batch_017_inputs,
  batch_018_inputs,
  batch_019_inputs,
  batch_020_inputs,
  batch_021_inputs,
  batch_022_inputs,
  batch_023_inputs,
  batch_024_inputs,
  batch_025_inputs,
  batch_026_inputs,
  batch_027_inputs,
  batch_028_inputs,
  batch_029_inputs,
  batch_030_inputs,
  batch_031_inputs,
  batch_032_inputs,
  batch_033_inputs,
  batch_034_inputs,
  batch_035_inputs,
  batch_036_inputs,
  batch_037_inputs,
  batch_038_inputs,
  batch_039_inputs,
  batch_040_inputs,
  batch_041_inputs,
  batch_042_inputs,
  batch_043_inputs,
  batch_044_inputs,
  batch_045_inputs,
  batch_046_inputs,
  batch_047_inputs,
  batch_048_inputs,
  batch_049_inputs,
  batch_050_inputs,
  batch_051_inputs
]

theorem shared_batched_checks : List.Forall (List.Forall Comparison.Check) sharedBatches :=
  ⟨batch_001_checks,
    batch_002_checks,
    batch_003_checks,
    batch_004_checks,
    batch_005_checks,
    batch_006_checks,
    batch_007_checks,
    batch_008_checks,
    batch_009_checks,
    batch_010_checks,
    batch_011_checks,
    batch_012_checks,
    batch_013_checks,
    batch_014_checks,
    batch_015_checks,
    batch_016_checks,
    batch_017_checks,
    batch_018_checks,
    batch_019_checks,
    batch_020_checks,
    batch_021_checks,
    batch_022_checks,
    batch_023_checks,
    batch_024_checks,
    batch_025_checks,
    batch_026_checks,
    batch_027_checks,
    batch_028_checks,
    batch_029_checks,
    batch_030_checks,
    batch_031_checks,
    batch_032_checks,
    batch_033_checks,
    batch_034_checks,
    batch_035_checks,
    batch_036_checks,
    batch_037_checks,
    batch_038_checks,
    batch_039_checks,
    batch_040_checks,
    batch_041_checks,
    batch_042_checks,
    batch_043_checks,
    batch_044_checks,
    batch_045_checks,
    batch_046_checks,
    batch_047_checks,
    batch_048_checks,
    batch_049_checks,
    batch_050_checks,
    batch_051_checks⟩

theorem shared_check_count : sharedBatches.flatten.length = 10155 :=
  List.length_flatten.trans (rfl : (sharedBatches.map List.length).sum = 10155)

theorem shared_checked (row : Comparison) (h : row ∈ sharedBatches.flatten) : row.Check := by
  obtain ⟨batch, hb, hr⟩ := List.mem_flatten.mp h
  have hbatch := List.forall_iff_forall_mem.mp shared_batched_checks batch hb
  exact List.forall_iff_forall_mem.mp hbatch row hr

#print axioms shared_checked

end ZetaGridChecks
