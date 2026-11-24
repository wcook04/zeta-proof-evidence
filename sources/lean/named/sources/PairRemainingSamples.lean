module

public import PairEnclosure
public meta import PairEnclosure

@[expose] public section

open Enclosure
namespace PairEvaluation

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem logSample1 :
    0 < Zeta.hardyZ (sfrac false 200711206799425567 68719476736000) ∧
    |stabilized (sfrac false 200711206799425567 68719476736000) - (13002326165933 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 200711206799425567 68719476736000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample1

theorem logSample2 :
    0 < Zeta.hardyZ (sfrac false 200727274888667229 68719476736000) ∧
    |stabilized (sfrac false 200727274888667229 68719476736000) - (12972240771273 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 200727274888667229 68719476736000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample2

theorem logSample3 :
    0 < Zeta.hardyZ (sfrac false 401414379554230303 137438953472000) ∧
    |stabilized (sfrac false 401414379554230303 137438953472000) - (12455772357957 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 401414379554230303 137438953472000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample3

theorem logSample4 :
    0 < Zeta.hardyZ (sfrac false 401462583821955289 137438953472000) ∧
    |stabilized (sfrac false 401462583821955289 137438953472000) - (12410609372729 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 401462583821955289 137438953472000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample4

theorem logSample5 :
    0 < Zeta.hardyZ (sfrac false 1605633416083058719 549755813888000) ∧
    |stabilized (sfrac false 1605633416083058719 549755813888000) - (11161579474300 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 1605633416083058719 549755813888000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample5

theorem logSample6 :
    0 < Zeta.hardyZ (sfrac false 1605874437421683649 549755813888000) ∧
    |stabilized (sfrac false 1605874437421683649 549755813888000) - (11105081710032 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have cert := pairStabilized% 32 768 1605874437421683649 549755813888000 1000000000000000000000000000000
  exact ⟨cert.1, moveCenter cert.2 (by norm_num [sfrac])⟩

#print axioms logSample6

end PairEvaluation
