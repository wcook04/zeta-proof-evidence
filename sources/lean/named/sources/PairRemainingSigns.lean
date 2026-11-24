module

public import PairEnclosure
public meta import PairEnclosure

@[expose] public section

open Enclosure
namespace PairEvaluation

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem hardy2391Right : Zeta.hardyZ (sfrac false 3828109221550209197 1310720000000000) > 0 :=
  pairHardySign% 32 768 3828109221550209197 1310720000000000 1000000000000000000000000000000

#print axioms hardy2391Right

theorem hardy2392Left : Zeta.hardyZ (sfrac false 3920611502603148204147 1342177280000000000) > 0 :=
  pairHardySign% 32 768 3920611502603148204147 1342177280000000000 1000000000000000000000000000000

#print axioms hardy2392Left

theorem hardy2392Right : Zeta.hardyZ (sfrac false 3920611502603416639603 1342177280000000000) < 0 :=
  pairHardySign% 32 768 3920611502603416639603 1342177280000000000 1000000000000000000000000000000

#print axioms hardy2392Right

end PairEvaluation
