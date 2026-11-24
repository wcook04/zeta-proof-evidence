module

public import MercuriXiRankedKernel
public import OriginalSourcePair

/-! Named strict Lehmer-pair certificate using the original counted source atlas. -/

@[expose] public section

namespace ZetaMercuriXi

open Complex ZetaFiniteHeight

/-- The 2,391st and 2,392nd positive zeros in the original complete ordered
count have both the full projected score and the critical-line score below
0.799974782. The original count identifies the roots, the four narrow signs
certify the root boxes, and the seven ordinary function values certify the
numerical upper bound. -/
theorem originalPair2391_2392_strict :
    ∃ a b : RiemannXiZerosIndex,
      riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (799974782 / 10 ^ 9) := by
  have hsimple (z : ℂ) (hz : riemannZeta z = 0)
      (hreg : z.im ∈ Set.Ioo 0 (gramPoint ZetaSourceRows.originalCount.minIdx)) :
      meromorphicOrderAt riemannZeta z = 1 := by
    obtain ⟨i, hi⟩ := ZetaSourceRows.originalAtlas.complete z hreg hz
    rw [hi]
    exact ZetaSourceRows.original_pair_simple i
  exact pair2391_of_ranked_atlas ZetaSourceRows.originalPlacement
    ZetaSourceRows.originalCount_height_ge_10000 hsimple

/-- In particular, the named original pair passes the strict Lehmer threshold. -/
theorem originalPair2391_2392_lehmer :
    ∃ a b : RiemannXiZerosIndex,
      riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (4 / 5) := by
  obtain ⟨a, b, ha, hb, hr, hprojected, hline⟩ := originalPair2391_2392_strict
  have hcut : (799974782 / 10 ^ 9 : ℝ) < 4 / 5 := by norm_num
  exact ⟨a, b, ha, hb, hr, hprojected.trans hcut, hline.trans hcut⟩

end ZetaMercuriXi

#print axioms ZetaMercuriXi.originalPair2391_2392_strict

#print axioms ZetaMercuriXi.originalPair2391_2392_lehmer

end
