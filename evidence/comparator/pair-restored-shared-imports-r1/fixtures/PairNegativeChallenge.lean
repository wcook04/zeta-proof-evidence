module

public import MercuriXiRankedKernel
public import OriginalSourcePair
public import CSVBridge
public import Mathlib.Data.Fin.VecNotation

public import CSVNamed
public import CSVNormalization
public import LogRobustness
public import AbsoluteWitness

@[expose] public section

namespace ZetaComparator

open Complex ZetaFiniteHeight ZetaMercuriXi ZetaCSV ZetaLogRobustness ZetaAbsoluteWitness

theorem pairStrict :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (4 / 5) := by
  sorry

theorem pairLehmer :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (4 / 5) := by
  sorry

theorem pairClassical :
    ∃ a b : Index,
      ZetaMercuriXi.riemannXiZeros a =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      (csvScore a b).im = 0 ∧
      0 < (csvScore a b).re ∧ (csvScore a b).re < (799974782 / 10 ^ 9 : ℝ) := by
  sorry

theorem classicalRootArgument (s : ℂ) : h₀Argument (2 * xiPlaneRoot s) = s := by
  sorry

theorem classicalArgumentRoot (x : ℂ) : 2 * xiPlaneRoot (h₀Argument x) = x := by
  sorry

theorem classicalNormalizedValue (s : ℂ) : csvH₀ (2 * xiPlaneRoot s) = riemannXi s / 8 := by
  sorry

theorem classicalNormalizedOrder (s : ℂ) :
    analyticOrderAt csvH₀ (2 * xiPlaneRoot s) = analyticOrderAt riemannXi s := by
  sorry

theorem pairRelativeRobust :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b robustScoreCutoff ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ logRadius) →
        pairObservation a b + weightedLogDelta e ≤ widenedObservation := by
  sorry

theorem pairAbsoluteRobust :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (799994453 / 10 ^ 9) ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ 3 / 10 ^ 9) →
        widenedPairObservation a b e ≤ observedUpper := by
  sorry

end ZetaComparator

end
