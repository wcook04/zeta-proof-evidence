import Zeta.RiemannSiegel.Linear
import C1ClosedForm

open RSC1

namespace Zeta.RiemannSiegel

/-- Mercuri's normalized linear Riemann–Siegel coefficient has magnitude below (1/8)
on the closed unit interval. The certificate also includes the removable zero locations
(1/4) and (3/4). -/
theorem abs_correctionLinear_lt_eighth {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |correctionLinear p| < 1 / 8 := by
  have hψ : ContDiff ℝ 3 correction :=
    contDiff_of_differentiable_iteratedDeriv fun j _ ↦ differentiable_iteratedDeriv_correction j
  rw [correctionLinear_eq]
  exact abs_normalized_third_lt_eighth_of_cos hψ cos_mul_correction hp0 hp1

end Zeta.RiemannSiegel

#print axioms Zeta.RiemannSiegel.abs_correctionLinear_lt_eighth
