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
      PairRoots a b ∧ PairScoresBelow a b (799974782 / 10 ^ 9) := ZetaMercuriXi.originalPair2391_2392_strict

theorem pairLehmer :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (4 / 5) := ZetaMercuriXi.originalPair2391_2392_lehmer

theorem pairClassical :
    ∃ a b : Index,
      ZetaMercuriXi.riemannXiZeros a =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      (csvScore a b).im = 0 ∧
      0 < (csvScore a b).re ∧ (csvScore a b).re < (799974782 / 10 ^ 9 : ℝ) := ZetaCSV.originalPair2391_2392_csv

theorem classicalRootArgument (s : ℂ) : h₀Argument (2 * xiPlaneRoot s) = s := ZetaCSV.h₀Argument_scaledRoot s

theorem classicalArgumentRoot (x : ℂ) : 2 * xiPlaneRoot (h₀Argument x) = x := ZetaCSV.scaledRoot_h₀Argument x

theorem classicalNormalizedValue (s : ℂ) : csvH₀ (2 * xiPlaneRoot s) = riemannXi s / 8 := ZetaCSV.csvH₀_at_scaledRoot s

theorem classicalNormalizedOrder (s : ℂ) :
    analyticOrderAt csvH₀ (2 * xiPlaneRoot s) = analyticOrderAt riemannXi s := ZetaCSV.csvH₀_order s

theorem pairRelativeRobust :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b robustScoreCutoff ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ logRadius) →
        pairObservation a b + weightedLogDelta e ≤ widenedObservation := ZetaLogRobustness.originalPair2391_2392_robust

theorem pairAbsoluteRobust :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (799994453 / 10 ^ 9) ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ 3 / 10 ^ 9) →
        widenedPairObservation a b e ≤ observedUpper := ZetaAbsoluteWitness.originalPair2391_2392_widened_absolute

end ZetaComparator

end
