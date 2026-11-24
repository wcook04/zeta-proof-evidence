module

public import AbsoluteSamples
public import MercuriXiRankedKernel
public import OriginalSourcePair
public import Zeta.ArgZeta.ShiftIdentity
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Independent widened observation proof for the signed absolute-tail transfer. -/

@[expose] public section


/-! Positivity of the Dirichlet series for the negative logarithmic derivative of zeta
at a real argument greater than one. -/

namespace ZetaRemoteMass

open ArithmeticFunction
open scoped ComplexOrder LSeries.notation
open ZetaFiniteHeight

theorem re_logDeriv_zeta_nonpos {t : ℝ} (ht : 1 < t) :
    (logDeriv riemannZeta (t : ℂ)).re ≤ 0 := by
  have ht' : 1 < (t : ℂ).re := by simpa using ht
  have hterm (n : ℕ) : 0 ≤ (LSeries.term ↗Λ (t : ℂ) n).re := by
    exact (Complex.nonneg_iff.mp
      (LSeries.term_nonneg (Complex.zero_le_real.mpr (vonMangoldt_nonneg (n := n))) t)).1
  have hseries : 0 ≤ (LSeries ↗Λ (t : ℂ)).re := by
    change 0 ≤ (∑' n, LSeries.term ↗Λ (t : ℂ) n).re
    rw [Complex.re_tsum (LSeriesSummable_vonMangoldt ht')]
    exact tsum_nonneg hterm
  have heq : logDeriv riemannZeta (t : ℂ) = -LSeries ↗Λ (t : ℂ) := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div ht', neg_div, neg_neg]
  rw [heq, Complex.neg_re]
  exact neg_nonpos.mpr hseries

/-- Upper bound for the right-hand side of the explicit formula at 10,000. -/
theorem explicit_formula_upper_10000 :
    (logDeriv riemannZeta (height : ℂ)).re + (1 / (height : ℂ)).re
        + (1 / ((height : ℂ) - 1)).re - 1 / 2 * Real.log Real.pi
        + 1 / 2 * (Complex.digamma (height / 2 : ℂ)).re
      ≤ 9 / 2 + 1 / height + 1 / (height - 1) := by
  have hzeta := re_logDeriv_zeta_nonpos (t := height) (by norm_num [height])
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg
    ((by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
  have hpsi : (Complex.digamma (height / 2 : ℂ)).re ≤ 9 :=
    digamma_half_height_le.trans log_half_height_lt.le
  have hdiv (x : ℝ) : (1 / (x : ℂ)).re = 1 / x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsub : (height : ℂ) - 1 = ((height - 1 : ℝ) : ℂ) := by simp
  rw [hsub, hdiv height, hdiv (height - 1)]
  linarith

/-- The explicit formula suffices for the signed tail estimate once the resolvent is summable. -/
theorem tailMass_of_explicit_formula_10000 {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hs : Summable (fun i ↦ resolvent height (ρ i)))
    (heq : (∑' i, resolvent height (ρ i)) =
      (logDeriv riemannZeta (height : ℂ)).re + (1 / (height : ℂ)).re
        + (1 / ((height : ℂ) - 1)).re - 1 / 2 * Real.log Real.pi
        + 1 / 2 * (Complex.digamma (height / 2 : ℂ)).re) :
    let w (i : ι) := if height ≤ |(ρ i).im| then 1 / (ρ i).im ^ 2 else 0
    Summable w ∧ (∑' i, w i) ≤ massBound :=
  tailMass_of_resolvent ρ hstrip hs (heq.trans_le explicit_formula_upper_10000)

#print axioms re_logDeriv_zeta_nonpos
#print axioms explicit_formula_upper_10000
#print axioms tailMass_of_explicit_formula_10000

end ZetaRemoteMass


/-! The signed remote mass at height 10,000 for the multiplicity-weighted
zero enumeration in Mercuri's zeta development. -/

namespace ZetaRemoteMass

open ZetaFiniteHeight

noncomputable section

private theorem height_ne_xi_zero (i : RiemannXiZerosIndex) :
    (height : ℂ) ≠ riemannXiZeros i := by
  intro heq
  have h := riemannXiZeros_re_lt_one i
  rw [← heq, Complex.ofReal_re] at h
  norm_num [height] at h

theorem summable_xi_resolvent :
    Summable (fun i : RiemannXiZerosIndex ↦ resolvent height (riemannXiZeros i)) := by
  simp_rw [resolvent_eq_re_inv]
  exact summable_re_inv_riemannXiZeros_sub height_ne_xi_zero

/-- Mercuri's explicit formula at the real point used for the tail bound. -/
theorem xi_resolvent_eq :
    (∑' i : RiemannXiZerosIndex, resolvent height (riemannXiZeros i))
      = (logDeriv riemannZeta (height : ℂ)).re + (1 / (height : ℂ)).re
        + (1 / ((height : ℂ) - 1)).re - 1 / 2 * Real.log Real.pi
        + 1 / 2 * (Complex.digamma (height / 2 : ℂ)).re := by
  simp_rw [resolvent_eq_re_inv]
  have height_ne_one : (height : ℂ) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [height] at hre
  exact tsum_re_inv_riemannXiZeros_sub_eq (s := (height : ℂ))
    (by norm_num [height]) height_ne_one height_ne_xi_zero
    (summable_re_inv_riemannXiZeros_sub height_ne_xi_zero)

/-- A bound before passage to the inverse-square ordinate weights. -/
theorem xi_resolvent_bound :
    (∑' i : RiemannXiZerosIndex, resolvent height (riemannXiZeros i))
      ≤ 9 / 2 + 1 / height + 1 / (height - 1) :=
  xi_resolvent_eq.trans_le explicit_formula_upper_10000

/-- The cutoff includes both signs of the ordinate and counts multiplicities. -/
theorem xi_remote_mass_10000 :
    let w (i : RiemannXiZerosIndex) :=
      if height ≤ |(riemannXiZeros i).im| then 1 / (riemannXiZeros i).im ^ 2 else 0
    Summable w ∧ (∑' i, w i) ≤ massBound := by
  exact tailMass_of_explicit_formula_10000 riemannXiZeros
    (fun i ↦ ⟨(riemannXiZeros_re_pos i).le, (riemannXiZeros_re_lt_one i).le⟩)
    summable_xi_resolvent xi_resolvent_eq

/-- The same bound applies after removing the certified pair or any other indices. -/
theorem xi_remote_mass_subtype (s : Set RiemannXiZerosIndex) :
    let w (i : RiemannXiZerosIndex) :=
      if height ≤ |(riemannXiZeros i).im| then 1 / (riemannXiZeros i).im ^ 2 else 0
    Summable (fun i : s ↦ w i.1) ∧ (∑' i : s, w i.1) ≤ massBound := by
  classical
  let w (i : RiemannXiZerosIndex) :=
    if height ≤ |(riemannXiZeros i).im| then 1 / (riemannXiZeros i).im ^ 2 else 0
  have hs : Summable w := xi_remote_mass_10000.1
  have hb : (∑' i, w i) ≤ massBound := xi_remote_mass_10000.2
  exact ⟨hs.subtype s, (hs.tsum_subtype_le w s (fun i ↦ by dsimp [w]; split_ifs <;> positivity)).trans hb⟩

theorem xi_remote_mass_lt_10_div_9999 :
    (∑' i : RiemannXiZerosIndex,
      if height ≤ |(riemannXiZeros i).im| then 1 / (riemannXiZeros i).im ^ 2 else 0)
      < 10 / 9999 := by
  exact xi_remote_mass_10000.2.trans_lt (by norm_num [massBound, height])

#print axioms summable_xi_resolvent
#print axioms xi_resolvent_eq
#print axioms xi_resolvent_bound
#print axioms xi_remote_mass_10000
#print axioms xi_remote_mass_subtype
#print axioms xi_remote_mass_lt_10_div_9999

end
end ZetaRemoteMass

namespace ZetaAbsoluteWitness

open Complex ZetaFiniteHeight Enclosure
open PairEvaluation hiding rootRadius

noncomputable section

private theorem weightedObservationWidened {a b f0 f1 f2 f3 f4 f5 f6 : ℝ}
    (ha : |a - (proxyMidpoint - proxyHalfGap)| ≤ rootRadius)
    (hb : |b - (proxyMidpoint + proxyHalfGap)| ≤ rootRadius)
    (hf0 : |f0 - (13286997882701 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf1 : |f1 - (13002326165933 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf2 : |f2 - (12972240771273 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf3 : |f3 - (12455772357957 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf4 : |f4 - (12410609372729 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf5 : |f5 - (11161579474300 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hf6 : |f6 - (11105081710032 : ℝ) / 1000000000000| ≤ 3005 / 1000000000000)
    (hr1 : |logCorrection WideMoment.s₁ maxNormalizedSq - (-287682072167 : ℝ) / 1000000000000| ≤ 1 / 1000000000000)
    (hr2 : |logCorrection WideMoment.s₂ maxNormalizedSq - (-826678572085 : ℝ) / 1000000000000| ≤ 1 / 1000000000000)
    (hr3 : |logCorrection WideMoment.s₃ maxNormalizedSq - (-2111190233786 : ℝ) / 1000000000000| ≤ 1 / 1000000000000) :
    let x := ((proxyMidpoint - a) / proxyHalfGap) ^ 2
    let y := ((b - proxyMidpoint) / proxyHalfGap) ^ 2
    WideMoment.upper
      (symmetric f0 f1 f2 + logCorrection WideMoment.s₁ x + logCorrection WideMoment.s₁ y)
      (symmetric f0 f3 f4 + logCorrection WideMoment.s₂ x + logCorrection WideMoment.s₂ y)
      (symmetric f0 f5 f6 + logCorrection WideMoment.s₃ x + logCorrection WideMoment.s₃ y)
      ≤ ZetaFiniteHeight.observedUpper := by
  dsimp only
  have hda : |(proxyMidpoint - a) - proxyHalfGap| ≤ rootRadius := by
    simpa only [show proxyMidpoint - a - proxyHalfGap =
        -(a - (proxyMidpoint - proxyHalfGap)) by ring, abs_neg] using ha
  have hdb : |(b - proxyMidpoint) - proxyHalfGap| ≤ rootRadius := by
    simpa only [show b - proxyMidpoint - proxyHalfGap =
        b - (proxyMidpoint + proxyHalfGap) by ring] using hb
  have hxa := rootCoordinateBounds hda
  have hxb := rootCoordinateBounds hdb
  have hrootA := (WideMoment.root_corrections_mono hxa.1 hxa.2).2
  have hrootB := (WideMoment.root_corrections_mono hxb.1 hxb.2).2
  unfold logCorrection at *
  simp only [symmetric, WideMoment.upper] at hrootA hrootB ⊢
  unfold ZetaFiniteHeight.observedUpper
  linarith only [hrootA, hrootB,
    (abs_le.mp hf0).1, (abs_le.mp hf0).2, (abs_le.mp hf1).1, (abs_le.mp hf1).2,
    (abs_le.mp hf2).1, (abs_le.mp hf2).2, (abs_le.mp hf3).1, (abs_le.mp hf3).2,
    (abs_le.mp hf4).1, (abs_le.mp hf4).2, (abs_le.mp hf5).1, (abs_le.mp hf5).2,
    (abs_le.mp hf6).1, (abs_le.mp hf6).2, (abs_le.mp hr1).1, (abs_le.mp hr1).2,
    (abs_le.mp hr2).1, (abs_le.mp hr2).2, (abs_le.mp hr3).1, (abs_le.mp hr3).2]

private theorem ord0 : sfrac false 100359620422023199 34359738368000 = sampleOrdinate0 := by
  norm_num [sampleOrdinate0, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord1 : sfrac false 200711206799425567 68719476736000 = sampleOrdinate1 := by
  norm_num [sampleOrdinate1, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord2 : sfrac false 200727274888667229 68719476736000 = sampleOrdinate2 := by
  norm_num [sampleOrdinate2, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord3 : sfrac false 401414379554230303 137438953472000 = sampleOrdinate3 := by
  norm_num [sampleOrdinate3, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord4 : sfrac false 401462583821955289 137438953472000 = sampleOrdinate4 := by
  norm_num [sampleOrdinate4, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord5 : sfrac false 1605633416083058719 549755813888000 = sampleOrdinate5 := by
  norm_num [sampleOrdinate5, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem ord6 : sfrac false 1605874437421683649 549755813888000 = sampleOrdinate6 := by
  norm_num [sampleOrdinate6, proxyMidpoint, proxyHalfGap, sfrac_false_div]

private theorem widen {f c e : ℝ}
    (hf : |f - c| ≤ 5 / 1000000000000) (he : |e| ≤ 3 / 10 ^ 9) :
    |(f + e) - c| ≤ 3005 / 1000000000000 := by
  rw [show (f + e) - c = (f - c) + e by ring]
  exact (abs_add_le _ _).trans ((add_le_add hf he).trans (by norm_num))

open ZetaMercuriXi in
/-- Perturb the seven stabilized logarithms independently at their exact abscissae.
The two actual-root corrections are unchanged. -/
def widenedPairObservation (a b : ZetaMercuriXi.RiemannXiZerosIndex) (e : Fin 7 → ℝ) : ℝ :=
  let H := observation (activePair a b) ZetaFiniteHeight.midpoint halfGap
  WideMoment.upper (H (1/2) + (2 * e 0 - e 1 - e 2))
    (H (3/4) + (2 * e 0 - e 3 - e 4)) (H (15/16) + (2 * e 0 - e 5 - e 6))

open ZetaMercuriXi in
theorem widenedPairObservation_le {a b : ZetaMercuriXi.RiemannXiZerosIndex} {l r : ℝ}
    (roots : PairRoots a b) (ha : ZetaMercuriXi.riemannXiZeros a = linePoint l)
    (hb : ZetaMercuriXi.riemannXiZeros b = linePoint r) (e : Fin 7 → ℝ)
    (he : ∀ i, |e i| ≤ 3 / 10 ^ 9) :
    widenedPairObservation a b e ≤ observedUpper := by
  have hla : |l - (ZetaFiniteHeight.midpoint - halfGap)| ≤ rootRadius := by
    simpa [ha] using roots.leftBox
  have hrb : |r - (ZetaFiniteHeight.midpoint + halfGap)| ≤ rootRadius := by
    simpa [hb] using roots.rightBox
  have sign0 : 0 < Zeta.hardyZ sampleOrdinate0 := by
    simpa only [ord0] using PairEvaluation.logSample0.1
  have log0 := widen rawSample0 (he 0)
  rw [ord0] at log0
  have sign1 : 0 < Zeta.hardyZ sampleOrdinate1 := by
    simpa only [ord1] using PairEvaluation.logSample1.1
  have log1 := widen rawSample1 (he 1)
  rw [ord1] at log1
  have sign2 : 0 < Zeta.hardyZ sampleOrdinate2 := by
    simpa only [ord2] using PairEvaluation.logSample2.1
  have log2 := widen rawSample2 (he 2)
  rw [ord2] at log2
  have sign3 : 0 < Zeta.hardyZ sampleOrdinate3 := by
    simpa only [ord3] using PairEvaluation.logSample3.1
  have log3 := widen rawSample3 (he 3)
  rw [ord3] at log3
  have sign4 : 0 < Zeta.hardyZ sampleOrdinate4 := by
    simpa only [ord4] using PairEvaluation.logSample4.1
  have log4 := widen rawSample4 (he 4)
  rw [ord4] at log4
  have sign5 : 0 < Zeta.hardyZ sampleOrdinate5 := by
    simpa only [ord5] using PairEvaluation.logSample5.1
  have log5 := widen rawSample5 (he 5)
  rw [ord5] at log5
  have sign6 : 0 < Zeta.hardyZ sampleOrdinate6 := by
    simpa only [ord6] using PairEvaluation.logSample6.1
  have log6 := widen rawSample6 (he 6)
  rw [ord6] at log6
  have h₁ := observation_eq_stabilized_and_pair_corrections roots ha hb
    (q := 1/2) (by norm_num) (by norm_num) sign0
    (by simpa only [sampleOrdinate1, mul_comm halfGap] using sign1)
    (by simpa only [sampleOrdinate2, mul_comm halfGap] using sign2)
  have h₂ := observation_eq_stabilized_and_pair_corrections roots ha hb
    (q := 3/4) (by norm_num) (by norm_num) sign0
    (by simpa only [sampleOrdinate3, mul_comm halfGap] using sign3)
    (by simpa only [sampleOrdinate4, mul_comm halfGap] using sign4)
  have h₃ := observation_eq_stabilized_and_pair_corrections roots ha hb
    (q := 15/16) (by norm_num) (by norm_num) sign0
    (by simpa only [sampleOrdinate5, mul_comm halfGap] using sign5)
    (by simpa only [sampleOrdinate6, mul_comm halfGap] using sign6)
  unfold widenedPairObservation
  dsimp only
  rw [h₁, h₂, h₃]
  have hw := weightedObservationWidened hla hrb log0 log1 log2 log3 log4 log5 log6
    logRootCorrection1 logRootCorrection2 logRootCorrection3
  simp only [symmetric, sampleOrdinate0, sampleOrdinate1, sampleOrdinate2, sampleOrdinate3,
    sampleOrdinate4, sampleOrdinate5, sampleOrdinate6, mul_comm halfGap] at hw ⊢
  rw [show ((1 / 2 : ℝ) ^ 2) = WideMoment.s₁ by norm_num,
      show ((3 / 4 : ℝ) ^ 2) = WideMoment.s₂ by norm_num,
      show ((15 / 16 : ℝ) ^ 2) = WideMoment.s₃ by norm_num]
  unfold WideMoment.upper at hw ⊢
  linarith only [hw]

open ZetaMercuriXi in
private theorem pairObservation_le_absolute {a b : ZetaMercuriXi.RiemannXiZerosIndex} {l r : ℝ}
    (roots : PairRoots a b) (ha : ZetaMercuriXi.riemannXiZeros a = linePoint l)
    (hb : ZetaMercuriXi.riemannXiZeros b = linePoint r) :
    pairObservation a b ≤ observedUpper := by
  simpa [widenedPairObservation, pairObservation] using
    widenedPairObservation_le roots ha hb (fun _ ↦ 0) (fun _ ↦ by norm_num)

open ZetaMercuriXi in
/-- Absolute correction to the actual Xi score, using the signed Hadamard tail
and the exact observed cutoff rather than the relative projection theorem. -/
theorem xi_pair_absolute {a b : ZetaMercuriXi.RiemannXiZerosIndex} (roots : PairRoots a b)
    (hline : ∀ i : ZetaMercuriXi.RiemannXiZerosIndex, |(ZetaMercuriXi.riemannXiZeros i).im| < height →
      (ZetaMercuriXi.riemannXiZeros i).re = 1 / 2)
    (hactual : pairObservation a b ≤ observedUpper) :
    PairScoresBelow a b outwardUpper := by
  classical
  let active := activePair a b
  let ρ (i : {i // i ∉ active}) := ZetaMercuriXi.riemannXiZeros i
  have hstrip (i : {i // i ∉ active}) : 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1 :=
    ⟨(ZetaMercuriXi.riemannXiZeros_re_pos i).le, (ZetaMercuriXi.riemannXiZeros_re_lt_one i).le⟩
  have hsum : Summable fun i : {i // i ∉ active} ↦ ordinateCoordinate (ρ i) :=
    (summable_centered_squared_offsets hadamardData ZetaFiniteHeight.midpoint halfGap).subtype _
  have hn (i : {i // i ∉ active}) : (ρ i).im ≠ ZetaFiniteHeight.midpoint := by
    have hd := (WideMoment.pair2391_exterior_support (roots.exterior i)).1
    intro heq
    change (ZetaMercuriXi.riemannXiZeros i).im = ZetaFiniteHeight.midpoint at heq
    rw [heq, sub_self, abs_zero] at hd
    norm_num at hd
  have hmid : riemannXi (linePoint ZetaFiniteHeight.midpoint) ≠ 0 :=
    roots.sample_ne_zero (by norm_num) (by norm_num)
  have hobs (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 15 / 16) :
      HasSum (fun i : {i // i ∉ active} ↦ complexObservation (q ^ 2) (complexCoordinate (ρ i)))
        (observation active ZetaFiniteHeight.midpoint halfGap q) := by
    have hprod0 : 0 ≤ q * halfGap := mul_nonneg hq (by norm_num)
    have hprod : q * halfGap ≤ (15 / 16) * halfGap :=
      mul_le_mul_of_nonneg_right hq' (by norm_num)
    have hL := roots.sample_ne_zero (t := ZetaFiniteHeight.midpoint - q * halfGap) (by linarith) (by linarith)
    have hR := roots.sample_ne_zero (t := ZetaFiniteHeight.midpoint + q * halfGap) (by linarith) (by linarith)
    have h := hasSum_deflatedXi_scaledComplexProbe_of_hadamard hadamardData
      active ZetaFiniteHeight.midpoint halfGap q hL hmid hR
    have he (i : {i // i ∉ active}) :
        complexCoordinate (ρ i) = centeredComplexOffset ZetaFiniteHeight.midpoint halfGap (ρ i) :=
      complexCoordinate_eq_div_I (hn i)
    convert h using 1
    funext i
    simp only [complexObservation, he, ρ]
  obtain ⟨hmass, hbound⟩ := ZetaRemoteMass.xi_remote_mass_subtype
    ({i : _root_.RiemannXiZerosIndex | i ∉ active} : Set _root_.RiemannXiZerosIndex)
  refine pair2391_of_finiteHeight ρ roots.leftBox roots.rightBox roots.exterior
    hstrip (fun i ↦ hline i) hsum hmass hbound ?_ ?_ ?_ hactual
  · simpa only [show ((1 / 2 : ℝ) ^ 2) = WideMoment.s₁ by norm_num] using
      hobs (1 / 2) (by norm_num) (by norm_num)
  · simpa only [show ((3 / 4 : ℝ) ^ 2) = WideMoment.s₂ by norm_num] using
      hobs (3 / 4) (by norm_num) (by norm_num)
  · simpa only [show ((15 / 16 : ℝ) ^ 2) = WideMoment.s₃ by norm_num] using
      hobs (15 / 16) (by norm_num) (by norm_num)

open ZetaMercuriXi in
/-- The original counted pair with no added premises. Both scores satisfy the
widened absolute-tail cutoff, and every independently widened observation
obeys the original fixed observed-input bound. -/
theorem originalPair2391_2392_widened_absolute :
    ∃ a b : ZetaMercuriXi.RiemannXiZerosIndex,
      ZetaMercuriXi.riemannXiZeros a = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391) ∧
      ZetaMercuriXi.riemannXiZeros b = linePoint (ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392) ∧
      PairRoots a b ∧ PairScoresBelow a b (799994453 / 10 ^ 9) ∧
      ∀ e : Fin 7 → ℝ, (∀ i, |e i| ≤ 3 / 10 ^ 9) →
        widenedPairObservation a b e ≤ observedUpper := by
  have hT := ZetaSourceRows.originalCount_height_ge_10000
  have hT' : ZetaSourceRows.rightEdge < gramPoint ZetaSourceRows.originalCount.minIdx :=
    (by norm_num [ZetaSourceRows.rightEdge] : ZetaSourceRows.rightEdge < height).trans_le hT
  have hsimple (z : ℂ) (hz : riemannZeta z = 0)
      (hreg : z.im ∈ Set.Ioo 0 (gramPoint ZetaSourceRows.originalCount.minIdx)) :
      meromorphicOrderAt riemannZeta z = 1 := by
    obtain ⟨i, hi⟩ := ZetaSourceRows.originalAtlas.complete z hreg hz
    rw [hi]
    exact ZetaSourceRows.original_pair_simple i
  obtain ⟨l, r, hL, hR, hzL, hzR⟩ := narrowZeros
  obtain ⟨a, b, ha, hb, hr⟩ := xi_pair_of_atlas ZetaSourceRows.originalPlacement hT' hsimple hL hR hzL hzR
  obtain ⟨hl, hright⟩ := ZetaSourceRows.narrow_boxes_inside_source hL hR
  obtain ⟨⟨_, _, uniqL⟩, ⟨_, _, uniqR⟩⟩ := ZetaSourceRows.unique_rows ZetaSourceRows.originalPlacement hT'
  have hLeq : l = ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2391 :=
    (uniqL l ⟨hl, hzL⟩).trans (uniqL _ ⟨ZetaSourceRows.originalPlacement.lower,
      ZetaSourceRows.originalAtlas.vanishes _⟩).symm
  have hReq : r = ZetaSourceRows.originalAtlas.root ZetaSourceRows.idx2392 :=
    (uniqR r ⟨hright, hzR⟩).trans (uniqR _ ⟨ZetaSourceRows.originalPlacement.upper,
      ZetaSourceRows.originalAtlas.vanishes _⟩).symm
  obtain ⟨hp, hc⟩ := xi_pair_absolute hr (atlas_line_upto ZetaSourceRows.originalAtlas hT)
    (pairObservation_le_absolute hr ha hb)
  have hdec : outwardUpper < (799994453 / 10 ^ 9 : ℝ) := by norm_num [outwardUpper]
  exact ⟨a, b, ha.trans (congrArg linePoint hLeq), hb.trans (congrArg linePoint hReq),
    hr, ⟨hp.trans hdec, hc.trans hdec⟩, widenedPairObservation_le hr ha hb⟩

#print axioms widenedPairObservation_le
#print axioms xi_pair_absolute
#print axioms originalPair2391_2392_widened_absolute

end
end ZetaAbsoluteWitness

end
