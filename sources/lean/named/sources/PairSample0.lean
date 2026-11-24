module

public import PairEnclosure
public meta import PairEnclosure

@[expose] public section

open Enclosure
namespace PairEvaluation

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem logSample0 :
    0 < Zeta.hardyZ (sfrac false 100359620422023199 34359738368000) ∧
    |stabilized (sfrac false 100359620422023199 34359738368000) - (13286997882701 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 100359620422023199 34359738368000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample0

end PairEvaluation
