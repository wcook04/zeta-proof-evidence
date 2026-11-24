module

public import AbsoluteComponentProof

@[expose] public section

namespace ZetaComparatorComponents

open Complex ZetaFiniteHeight ZetaAbsoluteWitness ZetaMercuriXi

theorem component_widenedPairObservation_le {a b : ZetaMercuriXi.RiemannXiZerosIndex} {l r : ℝ}
    (roots : PairRoots a b) (ha : ZetaMercuriXi.riemannXiZeros a = linePoint l)
    (hb : ZetaMercuriXi.riemannXiZeros b = linePoint r) (e : Fin 7 → ℝ)
    (he : ∀ i, |e i| ≤ 3 / 10 ^ 9) :
    widenedPairObservation a b e ≤ observedUpper := by
  sorry

theorem component_xi_pair_absolute {a b : ZetaMercuriXi.RiemannXiZerosIndex} (roots : PairRoots a b)
    (hline : ∀ i : ZetaMercuriXi.RiemannXiZerosIndex, |(ZetaMercuriXi.riemannXiZeros i).im| < height →
      (ZetaMercuriXi.riemannXiZeros i).re = 1 / 2)
    (hactual : pairObservation a b ≤ observedUpper) :
    PairScoresBelow a b outwardUpper := by
  sorry

end ZetaComparatorComponents

end
