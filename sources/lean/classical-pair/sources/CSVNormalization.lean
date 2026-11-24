module

public import CSVBridge

/-! The ordinate-variable normalization in CSV (1994), equation (1.3'). -/

@[expose] public section

namespace ZetaCSV

open Complex

noncomputable section

def h₀Argument (x : ℂ) : ℂ := 1 / 2 + x * (I / 2)

def csvH₀ (x : ℂ) : ℂ := riemannXi (h₀Argument x) / 8

theorem h₀Argument_scaledRoot (s : ℂ) : h₀Argument (2 * xiPlaneRoot s) = s := by
  have hi : (2 : ℂ) * xiPlaneRoot s * (I / 2) = xiPlaneRoot s * I := by ring
  unfold h₀Argument
  rw [hi]
  apply Complex.ext <;> simp [xiPlaneRoot, Complex.mul_re, Complex.mul_im]

theorem scaledRoot_h₀Argument (x : ℂ) : 2 * xiPlaneRoot (h₀Argument x) = x := by
  have hreal : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold h₀Argument
  rw [show I / 2 = ((1 / 2 : ℝ) : ℂ) * I by norm_num; ring, hreal]
  apply Complex.ext <;> simp [xiPlaneRoot, Complex.mul_re, Complex.mul_im] <;> ring

theorem csvH₀_at_scaledRoot (s : ℂ) : csvH₀ (2 * xiPlaneRoot s) = riemannXi s / 8 := by
  rw [csvH₀, h₀Argument_scaledRoot]

/-- The coordinate change has a nonzero derivative and preserves zero orders. -/
theorem csvH₀_order (s : ℂ) :
    analyticOrderAt csvH₀ (2 * xiPlaneRoot s) = analyticOrderAt riemannXi s := by
  let x := 2 * xiPlaneRoot s
  have hA : AnalyticAt ℂ h₀Argument x := by unfold h₀Argument; fun_prop
  have hd : deriv h₀Argument x ≠ 0 := by
    have hd' : HasDerivAt h₀Argument (I / 2) x := by
      change HasDerivAt (fun z : ℂ ↦ 1 / 2 + z * (I / 2)) (I / 2) x
      simpa only [one_mul] using (((hasDerivAt_id' x).mul_const (I / 2)).const_add (1 / 2))
    rw [hd'.deriv]
    exact div_ne_zero Complex.I_ne_zero (by norm_num)
  have hf : AnalyticAt ℂ (riemannXi ∘ h₀Argument) x :=
    (differentiable_riemannXi.analyticAt _).comp hA
  have hc : AnalyticAt ℂ (fun _ : ℂ ↦ (8 : ℂ)⁻¹) x := analyticAt_const
  have hc₀ : analyticOrderAt (fun _ : ℂ ↦ (8 : ℂ)⁻¹) x = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
  have he : csvH₀ = (riemannXi ∘ h₀Argument) * (fun _ : ℂ ↦ (8 : ℂ)⁻¹) := by
    funext y
    simp [csvH₀, div_eq_mul_inv]
  have hscale : h₀Argument x = s := h₀Argument_scaledRoot s
  change analyticOrderAt csvH₀ x = _
  rw [he, analyticOrderAt_mul hf hc, hc₀, add_zero,
    analyticOrderAt_comp_of_deriv_ne_zero hA hd, hscale]

#print axioms h₀Argument_scaledRoot
#print axioms scaledRoot_h₀Argument
#print axioms csvH₀_order

end
end ZetaCSV

end
