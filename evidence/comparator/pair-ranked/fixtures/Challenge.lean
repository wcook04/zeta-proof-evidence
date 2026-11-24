module

public import MercuriXiRankedKernel

@[expose] public section

namespace ZetaComparatorComponents

open Complex ZetaFiniteHeight ZetaMercuriXi

theorem component_pair2391_of_ranked_atlas {T : ℝ} {atlas : ZetaSourceRows.Atlas T}
    (placement : ZetaSourceRows.PairPlacement atlas) (hT : height ≤ T)
    (hsimple : ∀ s : ℂ, riemannZeta s = 0 → s.im ∈ Set.Ioo 0 T →
      meromorphicOrderAt riemannZeta s = 1) :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (atlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (atlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (799974782 / 10 ^ 9) := by
  sorry

end ZetaComparatorComponents

end
