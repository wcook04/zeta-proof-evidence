module

public import CSVBoundProof

@[expose] public section

namespace ZetaComparatorComponents

open Complex ZetaFiniteHeight ZetaCSV

theorem component_csvScore_bound {a b : Index} {B : ℝ} (roots : ZetaMercuriXi.PairRoots a b)
    (hprojected : ZetaMercuriXi.PairScoresBelow a b B) :
    Summable (fun i : Exterior a b ↦ ‖h₀Term (ZetaMercuriXi.riemannXiZeros a).im
      (ZetaMercuriXi.riemannXiZeros b).im (ZetaMercuriXi.riemannXiZeros i)‖) ∧
    (csvScore a b).im = 0 ∧ 0 < (csvScore a b).re ∧ (csvScore a b).re < B := by
  sorry

end ZetaComparatorComponents

end
