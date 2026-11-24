import C1Analytic
import C1TaylorCells
import C1DecimalCells
import Zeta.RiemannSiegel.Linear

open Real

namespace RSC1.Decimal

/-- The left-half sinc certificate suffices to bound the normalized third derivative on
the whole unit interval. The symmetry argument includes the two removable zeros. -/
private theorem abs_normalized_third_lt {bound : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hcos : ∀ p : ℝ, cos (2 * π * p) * ψ p = cos (2 * π * (p ^ 2 - p - 1 / 16)))
    (hjet : ∀ u : ℝ, -1 ≤ u → u ≤ 1 →
      |c1Jet u (sincJet 0 (c1ArgA u)) (sincJet 1 (c1ArgA u))
        (sincJet 2 (c1ArgA u)) (sincJet 3 (c1ArgA u))
        (sincJet 0 (c1ArgB u)) (sincJet 1 (c1ArgB u))
        (sincJet 2 (c1ArgB u)) (sincJet 3 (c1ArgB u))| < bound)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |-(iteratedDeriv 3 ψ p) / (96 * π ^ 2)| < bound := by
  have lowHalf (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
      |-(iteratedDeriv 3 ψ q) / (96 * π ^ 2)| < bound := by
    let u := 4 * q - 1
    have hu0 : -1 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have hq : (u + 1) / 4 = q := by dsimp [u]; ring
    have hj := hjet u hu0 hu1
    rw [c1Jet_eq_third_reparam hψ hcos hu0 hu1, third_reparam ψ hψ, hq] at hj
    rw [show -iteratedDeriv 3 ψ q / (96 * π ^ 2) =
      -(2 * ((1 / 4 : ℝ) ^ 3 * iteratedDeriv 3 ψ q) / (3 * π ^ 2)) by
        field_simp [pi_ne_zero]
        ring, abs_neg]
    exact hj
  by_cases hp : p ≤ 1 / 2
  · exact lowHalf p hp0 hp
  · have h := lowHalf (1-p) (by linarith) (by linarith)
    rw [abs_div, abs_neg,
      abs_third_symmetric_of_cos (hψ.differentiable (by norm_num)) hcos p] at h
    simpa only [abs_div, abs_neg] using h

private theorem normalizedThird_lt_ceiling {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hcos : ∀ p : ℝ, cos (2 * π * p) * ψ p = cos (2 * π * (p ^ 2 - p - 1 / 16)))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |-(iteratedDeriv 3 ψ p) / (96 * π ^ 2)| < (ceiling : ℝ) := by
  refine abs_normalized_third_lt hψ hcos ?_ hp0 hp1
  intro u hu0 hu1
  exact abs_c1Jet_lt_ceiling u
    (sincJet 0 (c1ArgA u)) (sincJet 1 (c1ArgA u)) (sincJet 2 (c1ArgA u)) (sincJet 3 (c1ArgA u))
    (sincJet 0 (c1ArgB u)) (sincJet 1 (c1ArgB u)) (sincJet 2 (c1ArgB u)) (sincJet 3 (c1ArgB u))
    hu0 hu1
    (sincJet_taylorPolynomial 0 (by norm_num) _) (sincJet_taylorPolynomial 1 (by norm_num) _)
    (sincJet_taylorPolynomial 2 (by norm_num) _) (sincJet_taylorPolynomial 3 (by norm_num) _)
    (sincJet_taylorPolynomial 0 (by norm_num) _) (sincJet_taylorPolynomial 1 (by norm_num) _)
    (sincJet_taylorPolynomial 2 (by norm_num) _) (sincJet_taylorPolynomial 3 (by norm_num) _)

end RSC1.Decimal

namespace Zeta.RiemannSiegel

/-- The normalized linear Riemann–Siegel coefficient has magnitude strictly below
the published rational ceiling 0.122459896 on the closed unit interval. -/
theorem abs_correctionLinear_lt_decimal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |correctionLinear p| < (122459896 : ℝ) / 1000000000 := by
  have hψ : ContDiff ℝ 3 correction :=
    contDiff_of_differentiable_iteratedDeriv fun j _ ↦ differentiable_iteratedDeriv_correction j
  rw [correctionLinear_eq]
  have h := RSC1.Decimal.normalizedThird_lt_ceiling hψ cos_mul_correction hp0 hp1
  unfold RSC1.Decimal.ceiling at h
  push_cast at h
  exact h

end Zeta.RiemannSiegel

#print axioms Zeta.RiemannSiegel.abs_correctionLinear_lt_decimal
