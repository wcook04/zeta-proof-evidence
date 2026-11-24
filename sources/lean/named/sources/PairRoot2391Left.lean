module

public import PairEnclosure
public meta import PairEnclosure

@[expose] public section

open Enclosure
namespace PairEvaluation

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem hardy2391Left : Zeta.hardyZ (sfrac false 3828109221549947053 1310720000000000) < 0 :=
  pairHardySign% 32 768 3828109221549947053 1310720000000000 1000000000000000000000000000000

#print axioms hardy2391Left

end PairEvaluation
