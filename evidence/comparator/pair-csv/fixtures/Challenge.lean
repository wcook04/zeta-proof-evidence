module

public import CSVNormalization
public import CSVRealityModule

@[expose] public section

namespace ZetaComparatorComponents

open Complex ZetaFiniteHeight ZetaCSV ZetaMercuriXi

open scoped BigOperators

theorem component_h₀Argument_scaledRoot (s : ℂ) : h₀Argument (2 * xiPlaneRoot s) = s := by
  sorry

theorem component_scaledRoot_h₀Argument (x : ℂ) : 2 * xiPlaneRoot (h₀Argument x) = x := by
  sorry

theorem component_csvH₀_at_scaledRoot (s : ℂ) : csvH₀ (2 * xiPlaneRoot s) = riemannXi s / 8 := by
  sorry

theorem component_csvH₀_order (s : ℂ) :
    analyticOrderAt csvH₀ (2 * xiPlaneRoot s) = analyticOrderAt riemannXi s := by
  sorry

theorem component_h₀Term_eq_complexTerm (a b : ℝ) (s : ℂ) : h₀Term a b s = complexTerm a b s := by
  sorry

theorem component_complexScore_comparison {ι : Type*} (ρ : ι → ℂ) {a b : ℝ}
    (ha : |a - (ZetaFiniteHeight.midpoint - halfGap)| ≤ rootRadius)
    (hb : |b - (ZetaFiniteHeight.midpoint + halfGap)| ≤ rootRadius)
    (hc : ∀ i, (ρ i).im ≤ 1459857 / 500 ∨ 2921761 / 1000 ≤ (ρ i).im)
    (hs : Summable (fun i ↦ ordinateCoordinate (ρ i))) :
    Summable (fun i ↦ ‖complexTerm a b (ρ i)‖) ∧
    Summable (fun i ↦ ordinateTerm a b (ρ i)) ∧
    (∑' i, complexTerm a b (ρ i)).re ≤ ∑' i, ordinateTerm a b (ρ i) := by
  sorry

theorem component_im_tsum_exterior_eq_zero_of_reflection {a b : ZetaMercuriXi.RiemannXiZerosIndex} (roots : PairRoots a b)
    (f : ℂ → ℂ) (hf : ∀ z, starRingEnd ℂ (f z) = f (1 - starRingEnd ℂ z)) :
    (∑' i : {i // i ∉ activePair a b}, f (ZetaMercuriXi.riemannXiZeros i.1)).im = 0 := by
  sorry

end ZetaComparatorComponents

end
