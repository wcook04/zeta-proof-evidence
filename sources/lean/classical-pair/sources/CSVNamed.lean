module

public import CSVBridge
public import MercuriXiNamedProof
public import CSVRealityModule

/-! The actual named pair satisfies the all-complex-zero CSV inequality. -/

@[expose] public section

namespace ZetaCSV

open Complex ZetaFiniteHeight
open scoped BigOperators

noncomputable section

abbrev Index := ZetaMercuriXi.RiemannXiZerosIndex

abbrev Exterior (a b : Index) := {i : Index // i ∉ ZetaMercuriXi.activePair a b}

def csvScore (a b : Index) : ℂ :=
  ∑' i : Exterior a b, h₀Term (ZetaMercuriXi.riemannXiZeros a).im
    (ZetaMercuriXi.riemannXiZeros b).im (ZetaMercuriXi.riemannXiZeros i)

private theorem root_order {a b : ℝ}
    (ha : |a - (ZetaFiniteHeight.midpoint - halfGap)| ≤ rootRadius)
    (hb : |b - (ZetaFiniteHeight.midpoint + halfGap)| ≤ rootRadius) : 0 < a ∧ a < b := by
  have hL := (abs_le.mp ha).1
  have hU := (abs_le.mp ha).2
  have hR := (abs_le.mp hb).1
  dsimp [ZetaFiniteHeight.midpoint, halfGap, rootRadius] at hL hU hR
  constructor <;> linarith

private theorem exterior_nonempty {a b : Index} (roots : ZetaMercuriXi.PairRoots a b) :
    Nonempty (Exterior a b) := by
  classical
  let z := ZetaMercuriXi.riemannXiZeros a
  have ho := root_order roots.leftBox roots.rightBox
  have hz : riemannXi z = 0 := ZetaMercuriXi.riemannXi_riemannXiZeros_eq_zero a
  have hconj : riemannXi (starRingEnd ℂ z) = 0 := by rw [riemannXi_conj, hz, map_zero]
  obtain ⟨i, hi⟩ := ZetaMercuriXi.exists_index_of_riemannXi_zero hconj
  have him : (ZetaMercuriXi.riemannXiZeros i).im < 0 := by
    rw [hi, Complex.conj_im]
    exact neg_neg_of_pos ho.1
  refine ⟨⟨i, ?_⟩⟩
  intro hm
  have hh : i = a ∨ i = b := by simpa [ZetaMercuriXi.activePair] using hm
  rcases hh with rfl | rfl
  · exact (not_lt_of_ge ho.1.le) him
  · exact (not_lt_of_ge (ho.1.trans ho.2).le) him

theorem csvScore_bound {a b : Index} {B : ℝ} (roots : ZetaMercuriXi.PairRoots a b)
    (hprojected : ZetaMercuriXi.PairScoresBelow a b B) :
    Summable (fun i : Exterior a b ↦ ‖h₀Term (ZetaMercuriXi.riemannXiZeros a).im
      (ZetaMercuriXi.riemannXiZeros b).im (ZetaMercuriXi.riemannXiZeros i)‖) ∧
    (csvScore a b).im = 0 ∧ 0 < (csvScore a b).re ∧ (csvScore a b).re < B := by
  let x := (ZetaMercuriXi.riemannXiZeros a).im
  let y := (ZetaMercuriXi.riemannXiZeros b).im
  let ρ (i : Exterior a b) := ZetaMercuriXi.riemannXiZeros i
  have hcoord : Summable (fun i : Exterior a b ↦ ordinateCoordinate (ρ i)) :=
    (ZetaMercuriXi.summable_centered_squared_offsets ZetaMercuriXi.hadamardData ZetaFiniteHeight.midpoint halfGap).subtype _
  obtain ⟨hnorm, _, hle⟩ := complexScore_comparison ρ roots.leftBox roots.rightBox roots.exterior hcoord
  have hnorm₀ : Summable (fun i : Exterior a b ↦ ‖h₀Term x y (ρ i)‖) := by
    simpa only [h₀Term_eq_complexTerm] using hnorm
  have hscore : csvScore a b = ∑' i : Exterior a b, complexTerm x y (ρ i) := by
    simp only [csvScore, h₀Term_eq_complexTerm, x, y, ρ]
  have him : (csvScore a b).im = 0 := by
    rw [hscore]
    exact ZetaMercuriXi.im_tsum_exterior_eq_zero_of_reflection roots (complexTerm x y)
      (complexTerm_reflect x y)
  have hpositive (i : Exterior a b) : 0 < (complexTerm x y (ρ i)).re := by
    have hd := endpoint_distance_gt_half roots.leftBox roots.rightBox (roots.exterior i)
    have hr₀ := ZetaMercuriXi.riemannXiZeros_re_pos i.1
    have hr₁ := ZetaMercuriXi.riemannXiZeros_re_lt_one i.1
    have hs : |1 / 2 - (ρ i).re| < 1 / 2 := abs_lt.mpr ⟨by dsimp [ρ]; linarith, by dsimp [ρ]; linarith⟩
    exact complexTerm_re_pos (ne_of_lt (root_order roots.leftBox roots.rightBox).2)
      (hs.trans hd.1) (hs.trans hd.2)
  obtain ⟨j⟩ := exterior_nonempty roots
  have hcomplex : Summable (fun i : Exterior a b ↦ complexTerm x y (ρ i)) := hnorm.of_norm
  have hre : HasSum (fun i : Exterior a b ↦ (complexTerm x y (ρ i)).re)
      (∑' i : Exterior a b, complexTerm x y (ρ i)).re :=
    Complex.reCLM.hasSum hcomplex.hasSum
  have hpos := hre.summable.tsum_pos (fun i ↦ (hpositive i).le) j (hpositive j)
  refine ⟨hnorm₀, him, ?_, ?_⟩
  · rw [hscore, ← hre.tsum_eq]
    exact hpos
  · rw [hscore]
    exact hle.trans_lt hprojected.1

/-- CSV's score for positive ordinates 2391 and 2392, including signed,
possibly nonreal zeros and multiplicities. -/
theorem originalPair2391_2392_csv :
    ∃ a b : Index,
      ZetaMercuriXi.riemannXiZeros a =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b =
        ZetaMercuriXi.linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      (csvScore a b).im = 0 ∧
      0 < (csvScore a b).re ∧ (csvScore a b).re < (799974782 / 10 ^ 9 : ℝ) := by
  obtain ⟨a, b, ha, hb, hr, hp⟩ := ZetaMercuriXi.originalPair2391_2392_strict
  obtain ⟨_, him, hp₀, hup⟩ := csvScore_bound hr hp
  exact ⟨a, b, ha, hb, him, hp₀, hup⟩

#print axioms csvScore_bound
#print axioms originalPair2391_2392_csv

end
end ZetaCSV

end
