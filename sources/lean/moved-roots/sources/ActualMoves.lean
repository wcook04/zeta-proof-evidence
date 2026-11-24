module

public meta import GridMargins
public import OriginalSourcePair
public import SourceRows
public import Zeta.Zeros.BuildCertsRS
public import Zeta.Zeros.Certificates.EulerMaclaurin.Batch0001
public import Zeta.Zeros.Certificates.Fold
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0003
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0004
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0005
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0006
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0007
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0008
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0009
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0010
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0011
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0012
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0013
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0014
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0015
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0016
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0017
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0018
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0019
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0020
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0021
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0022
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0023
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0024
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0025
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0026
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0027
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0028
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0029
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0030
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0031
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0032
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0033
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0034
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0035
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0036
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0037
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0038
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0039
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0040
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0041
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0042
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0043
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0044
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0045
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0046
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0047
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0048
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0049
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0050
public import Zeta.Zeros.Certificates.RiemannSiegel.Batch0051
public import Zeta.Zeros.IntervalRS

@[expose] public section

/- Proofs from MoveTransport.lean. -/
open Set

noncomputable section

namespace ZetaSourceRows

theorem zero_of_hardy_sign_product {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u)
    (hs : Zeta.hardyZ l * Zeta.hardyZ u < 0) :
    ∃ x ∈ Ioo l u, riemannZeta (linePoint x) = 0 :=
  riemannZeta.exists_zero_of_approx_sign_change hlu hl hs
    (by simpa using abs_pos.mpr (left_ne_zero_of_mul hs.ne))
    (by simpa using abs_pos.mpr (right_ne_zero_of_mul hs.ne))

/-- A new signed boundary cannot pass either of two neighboring uniquely isolated zeros.
    The sign at the unchanged outer site and at the new site gives a witness on the
    shortened side. Uniqueness in that original row identifies the witness. -/
theorem replace_boundary_preserves_roots {L old new U a b : ℝ}
    (hL : 0 ≤ L) (hnew : new ∈ Ioo L U)
    (ha : a ∈ Ioo L old) (hb : b ∈ Ioo old U)
    (uniqueA : ∀ x ∈ Ioo L old, riemannZeta (linePoint x) = 0 → x = a)
    (uniqueB : ∀ x ∈ Ioo old U, riemannZeta (linePoint x) = 0 → x = b)
    (signL : Zeta.hardyZ L * Zeta.hardyZ new < 0)
    (signR : Zeta.hardyZ new * Zeta.hardyZ U < 0) :
    a ∈ Ioo L new ∧ b ∈ Ioo new U := by
  rcases le_total new old with h | h
  · obtain ⟨x, hx, hzx⟩ := zero_of_hardy_sign_product hL hnew.1.le signL
    have he := uniqueA x ⟨hx.1, hx.2.trans_le h⟩ hzx
    exact ⟨he ▸ hx, ⟨h.trans_lt hb.1, hb.2⟩⟩
  · obtain ⟨x, hx, hzx⟩ := zero_of_hardy_sign_product (hL.trans hnew.1.le) hnew.2.le signR
    have he := uniqueB x ⟨h.trans_lt hx.1, hx.2⟩ hzx
    exact ⟨⟨ha.1, ha.2.trans_le h⟩, he ▸ hx⟩

/-- A checked ordered atlas gives membership uniqueness for any bracket whose other rows
    are separated from it. The proof uses completeness for actual zeta zeros. -/
theorem unique_in_ordered_row {T : ℝ} {atlas : Atlas T} {i : Fin 10156} {l u t : ℝ}
    (hL : 0 ≤ l) (hU : u ≤ T)
    (before : ∀ j : Fin 10156, j < i → atlas.root j ≤ l)
    (after : ∀ j : Fin 10156, i < j → u ≤ atlas.root j)
    (ht : t ∈ Ioo l u) (hz : riemannZeta (linePoint t) = 0) :
    t = atlas.root i := by
  obtain ⟨j, hj⟩ := atlas.complete (linePoint t)
    (by simpa using (show t ∈ Ioo 0 T from ⟨hL.trans_lt ht.1, ht.2.trans_le hU⟩)) hz
  have he : t = atlas.root j := by simpa using congrArg Complex.im hj
  rcases lt_trichotomy j i with h | rfl | h
  · exact False.elim ((not_lt_of_ge (he.trans_le (before j h))) ht.1)
  · exact he
  · exact False.elim ((not_lt_of_ge ((after j h).trans_eq he.symm)) ht.2)

/-- An actual replacement and its two neighboring original endpoints, as rational heights. -/
structure GridReplacement where
  site : ℕ
  lower : ℝ
  original : ℝ
  moved : ℝ
  upper : ℝ

def fiveReplacements : List GridReplacement := [
  ⟨106, 245466 / 1000, 247179 / 1000, 247551 / 1000, 248888 / 1000⟩,
  ⟨114, 259079 / 1000, 260767 / 1000, 260396 / 1000, 262452 / 1000⟩,
  ⟨184, 371556 / 1000, 373095 / 1000, 373431 / 1000, 374633 / 1000⟩,
  ⟨242, 458557 / 1000, 460021 / 1000, 459791 / 1000, 461484 / 1000⟩,
  ⟨378, 649537 / 1000, 650214 / 1000, 650467 / 1000, 652244 / 1000⟩]

theorem fiveReplacements_between {r : GridReplacement} (hr : r ∈ fiveReplacements) :
    0 ≤ r.lower ∧ r.moved ∈ Ioo r.lower r.upper := by
  simp only [fiveReplacements, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The five particular replacements preserve each pair's ordered root witnesses given
    original-row uniqueness and the true Hardy signs at the new and unchanged sites. -/
theorem fiveReplacements_preserve_roots {r : GridReplacement} (hr : r ∈ fiveReplacements)
    {a b : ℝ} (ha : a ∈ Ioo r.lower r.original) (hb : b ∈ Ioo r.original r.upper)
    (uniqueA : ∀ x ∈ Ioo r.lower r.original, riemannZeta (linePoint x) = 0 → x = a)
    (uniqueB : ∀ x ∈ Ioo r.original r.upper, riemannZeta (linePoint x) = 0 → x = b)
    (hL : 0 < Zeta.hardyZ r.lower) (hm : Zeta.hardyZ r.moved < 0)
    (hR : 0 < Zeta.hardyZ r.upper) : a ∈ Ioo r.lower r.moved ∧ b ∈ Ioo r.moved r.upper := by
  obtain ⟨hl, hm'⟩ := fiveReplacements_between hr
  exact replace_boundary_preserves_roots hl hm' ha hb uniqueA uniqueB
    (mul_neg_of_pos_of_neg hL hm) (mul_neg_of_neg_of_pos hm hR)

#print axioms replace_boundary_preserves_roots
#print axioms unique_in_ordered_row
#print axioms fiveReplacements_preserve_roots

end ZetaSourceRows

/- Proofs from MovedMargins.lean. -/
open Enclosure ZetaGrid

namespace ZetaGridChecks

theorem moved_legacy_106 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 247551 1000) := by
  rs_grid_margin 247551 1000 149500 1000 13 10 1 0
#print axioms moved_legacy_106

theorem moved_legacy_114 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 260396 1000) := by
  rs_grid_margin 260396 1000 149500 1000 13 10 1 0
#print axioms moved_legacy_114

theorem moved_legacy_184 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 373431 1000) := by
  rs_grid_margin 373431 1000 149500 1000 13 10 1 0
#print axioms moved_legacy_184

theorem moved_legacy_242 :
    error (sfrac false 13 10) (sfrac false 149500 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 459791 1000) := by
  rs_grid_margin 459791 1000 149500 1000 13 10 1 0
#print axioms moved_legacy_242

theorem moved_legacy_378 :
    error (sfrac false 13 10) (sfrac false 474603 1000) <
      (-1) * hardyZApproximantRS₀ (sfrac false 650467 1000) := by
  rs_grid_margin 650467 1000 474603 1000 13 10 1 0
#print axioms moved_legacy_378

end ZetaGridChecks

/- Proofs from MovedSigns.lean. -/
open BSN Enclosure

set_option autoImplicit false

namespace ZetaGridChecks

theorem hardyZ_negative_of_legacy_margin {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : 128 ≤ t)
    (hmargin : ZetaGrid.error (sfrac false 13 10) s < (-1) * hardyZApproximantRS₀ t) :
    Zeta.hardyZ t < 0 := by
  have hthreshold : 16 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have herr := (abs_le.mp (abs_hardyZRemainderRS₀_le hthreshold)).2
  have hdrop := hardyZErrorBoundRS₀_anti hs hst
  have hc : sfrac false 13 10 = (13 / 10 : ℝ) := by norm_num [sfrac]
  rw [hc] at hmargin
  change hardyZErrorBoundRS₀ s < (-1) * hardyZApproximantRS₀ t at hmargin
  change Zeta.hardyZ t - hardyZApproximantRS₀ t ≤ hardyZErrorBoundRS₀ t at herr
  linarith only [herr, hdrop, hmargin]

theorem hardyZ_moved_106 : Zeta.hardyZ (sfrac false 247551 1000) < 0 :=
  hardyZ_negative_of_legacy_margin (s := sfrac false 149500 1000)
    (by norm_num [sfrac]) (by norm_num [sfrac]) (by norm_num [sfrac]) moved_legacy_106

theorem hardyZ_moved_114 : Zeta.hardyZ (sfrac false 260396 1000) < 0 :=
  hardyZ_negative_of_legacy_margin (s := sfrac false 149500 1000)
    (by norm_num [sfrac]) (by norm_num [sfrac]) (by norm_num [sfrac]) moved_legacy_114

theorem hardyZ_moved_184 : Zeta.hardyZ (sfrac false 373431 1000) < 0 :=
  hardyZ_negative_of_legacy_margin (s := sfrac false 149500 1000)
    (by norm_num [sfrac]) (by norm_num [sfrac]) (by norm_num [sfrac]) moved_legacy_184

theorem hardyZ_moved_242 : Zeta.hardyZ (sfrac false 459791 1000) < 0 :=
  hardyZ_negative_of_legacy_margin (s := sfrac false 149500 1000)
    (by norm_num [sfrac]) (by norm_num [sfrac]) (by norm_num [sfrac]) moved_legacy_242

theorem hardyZ_moved_378 : Zeta.hardyZ (sfrac false 650467 1000) < 0 :=
  hardyZ_negative_of_legacy_margin (s := sfrac false 474603 1000)
    (by norm_num [sfrac]) (by norm_num [sfrac]) (by norm_num [sfrac]) moved_legacy_378

def movedHeights : List (ℕ × ℕ × ℕ) :=
  [(106, 247551, 1000), (114, 260396, 1000), (184, 373431, 1000),
    (242, 459791, 1000), (378, 650467, 1000)]

theorem all_moved_negative (row : ℕ × ℕ × ℕ) (h : row ∈ movedHeights) :
    Zeta.hardyZ (sfrac false row.2.1 row.2.2) < 0 := by
  have checked : List.Forall (fun p : ℕ × ℕ × ℕ ↦
      Zeta.hardyZ (sfrac false p.2.1 p.2.2) < 0) movedHeights :=
    ⟨hardyZ_moved_106, hardyZ_moved_114, hardyZ_moved_184, hardyZ_moved_242, hardyZ_moved_378⟩
  exact List.forall_iff_forall_mem.mp checked row h

#print axioms all_moved_negative

#print axioms hardyZ_moved_106
#print axioms hardyZ_moved_114
#print axioms hardyZ_moved_184
#print axioms hardyZ_moved_242
#print axioms hardyZ_moved_378

end ZetaGridChecks

/- Proofs from NeighborSigns.lean. -/
open Enclosure ZetaGrid

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace ZetaGridChecks

theorem positive_of_own_legacy_margin {t : ℝ} (ht : 128 ≤ t)
    (hmargin : ZetaGrid.error (sfrac false 13 10) t < 1 * hardyZApproximantRS₀ t) :
    0 < Zeta.hardyZ t := by
  have hthreshold : 16 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have herr := (abs_le.mp (abs_hardyZRemainderRS₀_le hthreshold)).1
  have hc : sfrac false 13 10 = (13 / 10 : ℝ) := by norm_num [sfrac]
  rw [hc] at hmargin
  change hardyZErrorBoundRS₀ t < 1 * hardyZApproximantRS₀ t at hmargin
  change -(hardyZErrorBoundRS₀ t) ≤ Zeta.hardyZ t - hardyZApproximantRS₀ t at herr
  linarith only [herr, hmargin]

theorem hardyZ_left_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 245466 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 245466 1000 245466 1000 13 10 0 0
#print axioms hardyZ_left_neighbor_106

theorem hardyZ_right_neighbor_106 : 0 < Zeta.hardyZ (sfrac false 248888 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 248888 1000 248888 1000 13 10 0 0
#print axioms hardyZ_right_neighbor_106

theorem hardyZ_left_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 259079 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 259079 1000 259079 1000 13 10 0 0
#print axioms hardyZ_left_neighbor_114

theorem hardyZ_right_neighbor_114 : 0 < Zeta.hardyZ (sfrac false 262452 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 262452 1000 262452 1000 13 10 0 0
#print axioms hardyZ_right_neighbor_114

theorem hardyZ_left_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 371556 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 371556 1000 371556 1000 13 10 0 0
#print axioms hardyZ_left_neighbor_184

theorem hardyZ_right_neighbor_184 : 0 < Zeta.hardyZ (sfrac false 374633 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 374633 1000 374633 1000 13 10 0 0
#print axioms hardyZ_right_neighbor_184

theorem hardyZ_left_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 458557 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 458557 1000 458557 1000 13 10 0 0
#print axioms hardyZ_left_neighbor_242

theorem hardyZ_right_neighbor_242 : 0 < Zeta.hardyZ (sfrac false 461484 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 461484 1000 461484 1000 13 10 0 0
#print axioms hardyZ_right_neighbor_242

theorem hardyZ_left_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 649537 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 649537 1000 649537 1000 13 10 0 0
#print axioms hardyZ_left_neighbor_378

theorem hardyZ_right_neighbor_378 : 0 < Zeta.hardyZ (sfrac false 652244 1000) := by
  apply positive_of_own_legacy_margin (by norm_num [sfrac])
  rs_grid_margin 652244 1000 652244 1000 13 10 0 0
#print axioms hardyZ_right_neighbor_378

end ZetaGridChecks

/- Proofs from MoveTrueSigns.lean. -/
open ZetaGridChecks

namespace ZetaSourceRows

/-- Actual pointwise Hardy signs at the five candidate boundaries and ten unchanged neighbors. -/
theorem fiveReplacements_trueSigns {r : GridReplacement} (hr : r ∈ fiveReplacements) :
    0 < Zeta.hardyZ r.lower ∧ Zeta.hardyZ r.moved < 0 ∧ 0 < Zeta.hardyZ r.upper := by
  simp only [fiveReplacements, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simpa [Enclosure.sfrac] using hardyZ_left_neighbor_106,
      by simpa [Enclosure.sfrac] using hardyZ_moved_106,
      by simpa [Enclosure.sfrac] using hardyZ_right_neighbor_106⟩
  · exact ⟨by simpa [Enclosure.sfrac] using hardyZ_left_neighbor_114,
      by simpa [Enclosure.sfrac] using hardyZ_moved_114,
      by simpa [Enclosure.sfrac] using hardyZ_right_neighbor_114⟩
  · exact ⟨by simpa [Enclosure.sfrac] using hardyZ_left_neighbor_184,
      by simpa [Enclosure.sfrac] using hardyZ_moved_184,
      by simpa [Enclosure.sfrac] using hardyZ_right_neighbor_184⟩
  · exact ⟨by simpa [Enclosure.sfrac] using hardyZ_left_neighbor_242,
      by simpa [Enclosure.sfrac] using hardyZ_moved_242,
      by simpa [Enclosure.sfrac] using hardyZ_right_neighbor_242⟩
  · exact ⟨by simpa [Enclosure.sfrac] using hardyZ_left_neighbor_378,
      by simpa [Enclosure.sfrac] using hardyZ_moved_378,
      by simpa [Enclosure.sfrac] using hardyZ_right_neighbor_378⟩

/-- No source row touches two moved sites, so the five local transfers can be applied
    simultaneously without changing either unchanged neighbor in a transferred interval. -/
theorem fiveReplacements_separatedSites : (fiveReplacements.map GridReplacement.site).Pairwise
    (fun a b ↦ a + 1 < b) := by
  change ([106, 114, 184, 242, 378] : List ℕ).Pairwise (fun a b ↦ a + 1 < b)
  decide

#print axioms fiveReplacements_trueSigns

end ZetaSourceRows

/- Proofs from EarlyDetailedRows.lean. -/
open Zeta.Certificates

namespace ZetaSourceRows

set_option maxRecDepth 10000 in
noncomputable def earlyFirst : CertifiedZeroIntervals := by
  build_certs_rs 0 200

set_option maxRecDepth 10000 in
noncomputable def earlySecond : CertifiedZeroIntervals := by
  build_certs_rs 200 400

set_option maxRecDepth 10000 in
/-- The original first two RS batches remain explicit for exact site-to-row lookup. -/
noncomputable def detailEarly : CertifiedZeroIntervals :=
  earlyFirst.append earlySecond (separated_of_endpoints (by rfl) (by rfl)
    (show Enclosure.sfrac false 474603 1000 ≤ Enclosure.sfrac false 474603 1000 from le_rfl))

set_option maxRecDepth 10000 in
@[simp] theorem detailEarly_length : detailEarly.intervals.length = 400 := by rfl

set_option maxRecDepth 10000 in
theorem detailEarly_head : detailEarly.intervals.head?.map (·.fst) =
    some (Enclosure.sfrac false 149500 1000) := by rfl

set_option maxRecDepth 10000 in
theorem detailEarly_last : detailEarly.intervals.getLast?.map (·.snd) =
    some (Enclosure.sfrac false 748976 1000) := by rfl

set_option maxRecDepth 10000 in
theorem earlyFirstSpec : BatchSpec 200 149500 1000 474603 1000 := by
  exact ⟨earlyFirst, rfl, rfl, rfl⟩

set_option maxRecDepth 10000 in
theorem earlySecondSpec : BatchSpec 200 474603 1000 748976 1000 := by
  exact ⟨earlySecond, rfl, rfl, rfl⟩

#print axioms earlyFirstSpec
#print axioms earlySecondSpec

end ZetaSourceRows

/- Proofs from OpaqueAfterEarly.lean. -/
open Zeta.Certificates

namespace ZetaSourceRows

theorem suffixThrough3 : BatchSpec 200 748976 1000 1004192 1000 :=
  RiemannSiegel.Batch0003.batch

theorem suffixThrough4 : BatchSpec 400 748976 1000 1246504 1000 :=
  BatchSpec.append suffixThrough3 RiemannSiegel.Batch0004.batch rfl rfl rfl

theorem suffixThrough5 : BatchSpec 600 748976 1000 1480141 1000 :=
  BatchSpec.append suffixThrough4 RiemannSiegel.Batch0005.batch rfl rfl rfl

theorem suffixThrough6 : BatchSpec 800 748976 1000 1707173 1000 :=
  BatchSpec.append suffixThrough5 RiemannSiegel.Batch0006.batch rfl rfl rfl

theorem suffixThrough7 : BatchSpec 1000 748976 1000 1928919 1000 :=
  BatchSpec.append suffixThrough6 RiemannSiegel.Batch0007.batch rfl rfl rfl

theorem suffixThrough8 : BatchSpec 1200 748976 1000 2146286 1000 :=
  BatchSpec.append suffixThrough7 RiemannSiegel.Batch0008.batch rfl rfl rfl

theorem suffixThrough9 : BatchSpec 1400 748976 1000 2359934 1000 :=
  BatchSpec.append suffixThrough8 RiemannSiegel.Batch0009.batch rfl rfl rfl

theorem suffixThrough10 : BatchSpec 1600 748976 1000 2570361 1000 :=
  BatchSpec.append suffixThrough9 RiemannSiegel.Batch0010.batch rfl rfl rfl

theorem suffixThrough11 : BatchSpec 1800 748976 1000 2777958 1000 :=
  BatchSpec.append suffixThrough10 RiemannSiegel.Batch0011.batch rfl rfl rfl

theorem suffixThrough12 : BatchSpec 2000 748976 1000 2983035 1000 :=
  BatchSpec.append suffixThrough11 RiemannSiegel.Batch0012.batch rfl rfl rfl

theorem suffixThrough13 : BatchSpec 2200 748976 1000 3185847 1000 :=
  BatchSpec.append suffixThrough12 RiemannSiegel.Batch0013.batch rfl rfl rfl

theorem suffixThrough14 : BatchSpec 2400 748976 1000 3386605 1000 :=
  BatchSpec.append suffixThrough13 RiemannSiegel.Batch0014.batch rfl rfl rfl

theorem suffixThrough15 : BatchSpec 2600 748976 1000 3585487 1000 :=
  BatchSpec.append suffixThrough14 RiemannSiegel.Batch0015.batch rfl rfl rfl

theorem suffixThrough16 : BatchSpec 2800 748976 1000 3782644 1000 :=
  BatchSpec.append suffixThrough15 RiemannSiegel.Batch0016.batch rfl rfl rfl

theorem suffixThrough17 : BatchSpec 3000 748976 1000 3977721 1000 :=
  BatchSpec.append suffixThrough16 RiemannSiegel.Batch0017.batch rfl rfl rfl

theorem suffixThrough18 : BatchSpec 3200 748976 1000 4172292 1000 :=
  BatchSpec.append suffixThrough17 RiemannSiegel.Batch0018.batch rfl rfl rfl

theorem suffixThrough19 : BatchSpec 3400 748976 1000 4364995 1000 :=
  BatchSpec.append suffixThrough18 RiemannSiegel.Batch0019.batch rfl rfl rfl

theorem suffixThrough20 : BatchSpec 3600 748976 1000 4556407 1000 :=
  BatchSpec.append suffixThrough19 RiemannSiegel.Batch0020.batch rfl rfl rfl

theorem suffixThrough21 : BatchSpec 3800 748976 1000 4746605 1000 :=
  BatchSpec.append suffixThrough20 RiemannSiegel.Batch0021.batch rfl rfl rfl

theorem suffixThrough22 : BatchSpec 4000 748976 1000 4935659 1000 :=
  BatchSpec.append suffixThrough21 RiemannSiegel.Batch0022.batch rfl rfl rfl

theorem suffixThrough23 : BatchSpec 4200 748976 1000 5123633 1000 :=
  BatchSpec.append suffixThrough22 RiemannSiegel.Batch0023.batch rfl rfl rfl

theorem suffixThrough24 : BatchSpec 4400 748976 1000 5310583 1000 :=
  BatchSpec.append suffixThrough23 RiemannSiegel.Batch0024.batch rfl rfl rfl

theorem suffixThrough25 : BatchSpec 4600 748976 1000 5496562 1000 :=
  BatchSpec.append suffixThrough24 RiemannSiegel.Batch0025.batch rfl rfl rfl

theorem suffixThrough26 : BatchSpec 4800 748976 1000 5681847 1000 :=
  BatchSpec.append suffixThrough25 RiemannSiegel.Batch0026.batch rfl rfl rfl

theorem suffixThrough27 : BatchSpec 5000 748976 1000 5865789 1000 :=
  BatchSpec.append suffixThrough26 RiemannSiegel.Batch0027.batch rfl rfl rfl

theorem suffixThrough28 : BatchSpec 5200 748976 1000 6049119 1000 :=
  BatchSpec.append suffixThrough27 RiemannSiegel.Batch0028.batch rfl rfl rfl

theorem suffixThrough29 : BatchSpec 5400 748976 1000 6231645 1000 :=
  BatchSpec.append suffixThrough28 RiemannSiegel.Batch0029.batch rfl rfl rfl

theorem suffixThrough30 : BatchSpec 5600 748976 1000 6413398 1000 :=
  BatchSpec.append suffixThrough29 RiemannSiegel.Batch0030.batch rfl rfl rfl

theorem suffixThrough31 : BatchSpec 5800 748976 1000 6594411 1000 :=
  BatchSpec.append suffixThrough30 RiemannSiegel.Batch0031.batch rfl rfl rfl

theorem suffixThrough32 : BatchSpec 6000 748976 1000 6774712 1000 :=
  BatchSpec.append suffixThrough31 RiemannSiegel.Batch0032.batch rfl rfl rfl

theorem suffixThrough33 : BatchSpec 6200 748976 1000 6954777 1000 :=
  BatchSpec.append suffixThrough32 RiemannSiegel.Batch0033.batch rfl rfl rfl

theorem suffixThrough34 : BatchSpec 6400 748976 1000 7133286 1000 :=
  BatchSpec.append suffixThrough33 RiemannSiegel.Batch0034.batch rfl rfl rfl

theorem suffixThrough35 : BatchSpec 6600 748976 1000 7311607 1000 :=
  BatchSpec.append suffixThrough34 RiemannSiegel.Batch0035.batch rfl rfl rfl

theorem suffixThrough36 : BatchSpec 6800 748976 1000 7489758 1000 :=
  BatchSpec.append suffixThrough35 RiemannSiegel.Batch0036.batch rfl rfl rfl

theorem suffixThrough37 : BatchSpec 7000 748976 1000 7666428 1000 :=
  BatchSpec.append suffixThrough36 RiemannSiegel.Batch0037.batch rfl rfl rfl

theorem suffixThrough38 : BatchSpec 7200 748976 1000 7842968 1000 :=
  BatchSpec.append suffixThrough37 RiemannSiegel.Batch0038.batch rfl rfl rfl

theorem suffixThrough39 : BatchSpec 7400 748976 1000 8018952 1000 :=
  BatchSpec.append suffixThrough38 RiemannSiegel.Batch0039.batch rfl rfl rfl

theorem suffixThrough40 : BatchSpec 7600 748976 1000 8193959 1000 :=
  BatchSpec.append suffixThrough39 RiemannSiegel.Batch0040.batch rfl rfl rfl

theorem suffixThrough41 : BatchSpec 7800 748976 1000 8369321 1000 :=
  BatchSpec.append suffixThrough40 RiemannSiegel.Batch0041.batch rfl rfl rfl

theorem suffixThrough42 : BatchSpec 8000 748976 1000 8543737 1000 :=
  BatchSpec.append suffixThrough41 RiemannSiegel.Batch0042.batch rfl rfl rfl

theorem suffixThrough43 : BatchSpec 8200 748976 1000 8717662 1000 :=
  BatchSpec.append suffixThrough42 RiemannSiegel.Batch0043.batch rfl rfl rfl

theorem suffixThrough44 : BatchSpec 8400 748976 1000 8891108 1000 :=
  BatchSpec.append suffixThrough43 RiemannSiegel.Batch0044.batch rfl rfl rfl

theorem suffixThrough45 : BatchSpec 8600 748976 1000 9063657 1000 :=
  BatchSpec.append suffixThrough44 RiemannSiegel.Batch0045.batch rfl rfl rfl

theorem suffixThrough46 : BatchSpec 8800 748976 1000 9236187 1000 :=
  BatchSpec.append suffixThrough45 RiemannSiegel.Batch0046.batch rfl rfl rfl

theorem suffixThrough47 : BatchSpec 9000 748976 1000 9408275 1000 :=
  BatchSpec.append suffixThrough46 RiemannSiegel.Batch0047.batch rfl rfl rfl

theorem suffixThrough48 : BatchSpec 9200 748976 1000 9579935 1000 :=
  BatchSpec.append suffixThrough47 RiemannSiegel.Batch0048.batch rfl rfl rfl

theorem suffixThrough49 : BatchSpec 9400 748976 1000 9751603 1000 :=
  BatchSpec.append suffixThrough48 RiemannSiegel.Batch0049.batch rfl rfl rfl

theorem suffixThrough50 : BatchSpec 9600 748976 1000 9922434 1000 :=
  BatchSpec.append suffixThrough49 RiemannSiegel.Batch0050.batch rfl rfl rfl

theorem opaqueAfterEarly : BatchSpec 9704 748976 1000 10011107 1000 :=
  BatchSpec.append suffixThrough50 RiemannSiegel.Batch0051.batch rfl rfl rfl

end ZetaSourceRows

/- Proofs from OriginalMovesIndexed.lean. -/
open Set Zeta.Certificates

noncomputable section

namespace ZetaSourceRows

abbrev em := EulerMaclaurin.Batch0001.batch

def first452 : CertifiedZeroIntervals := em.bundle.append detailEarly
  (separated_of_endpoints em.bundle_getLast? detailEarly_head le_rfl)

theorem first452_last : first452.intervals.getLast?.map (·.snd) =
    some (Enclosure.sfrac false 748976 1000) := by
  have hn : detailEarly.intervals ≠ [] := by
    intro h
    have hl := detailEarly_length
    rw [h] at hl
    contradiction
  unfold first452
  exact (congrArg (Option.map (·.snd))
    (CertifiedZeroIntervals.append_getLast? _ _ _ hn)).trans detailEarly_last

def movesGrid : CertifiedZeroIntervals := first452.append opaqueAfterEarly.bundle
  (separated_of_endpoints first452_last opaqueAfterEarly.bundle_head? le_rfl)

theorem movesGrid_length : movesGrid.intervals.length = 10156 := by
  simp [movesGrid, first452]

theorem movesGrid_below : movesGrid.height ≤ gramPoint originalCount.minIdx := by
  apply movesGrid.height_le_of_getLast?_snd (b := Enclosure.sfrac false 10011107 1000)
  · unfold movesGrid
    exact (congrArg (Option.map (·.snd))
      (CertifiedZeroIntervals.append_getLast? _ _ _ opaqueAfterEarly.bundle_ne)).trans
      opaqueAfterEarly.bundle_getLast?
  · exact (show Enclosure.sfrac false 10011107 1000 ≤ Gram.gp1.fst by
      norm_num [Enclosure.sfrac]).trans Gram.certifiedGramBlockSeq.head_left_le_gramPoint

def movesAtlas : Atlas (gramPoint originalCount.minIdx) :=
  fromMercuriCount originalCount originalGrid_length movesGrid movesGrid_length movesGrid_below

theorem moves_root_eq (i : Fin 10156) :
    movesAtlas.root i = gridRoot movesGrid movesGrid_length i := by
  unfold movesAtlas fromMercuriCount
  rfl

theorem independent_assembly_same_root : movesAtlas.root = originalAtlas.root :=
  same_ordinals movesAtlas originalAtlas

theorem idx_bounds {r : GridReplacement} (hr : r ∈ fiveReplacements) :
    53 ≤ r.site ∧ r.site < 452 := by
  simp only [fiveReplacements, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num

def leftMoveIndex (r : GridReplacement) (hr : r ∈ fiveReplacements) : Fin 10156 :=
  ⟨r.site - 1, (Nat.sub_le _ _).trans_lt ((idx_bounds hr).2.trans (by decide))⟩

def rightMoveIndex (r : GridReplacement) (hr : r ∈ fiveReplacements) : Fin 10156 :=
  ⟨r.site, (idx_bounds hr).2.trans (by decide)⟩

theorem middle_index {i : Fin 10156} (hl : 52 ≤ i.val) (hu : i.val < 452) :
    gridInterval movesGrid movesGrid_length i =
      detailEarly.intervals[i.val - 52]'(by rw [detailEarly_length]; omega) := by
  have hm := getElem?_middle em.bundle.intervals detailEarly.intervals
    opaqueAfterEarly.bundle.intervals (j := i.val - 52)
    (by rw [detailEarly_length]; omega)
  rw [em.bundle_length, show 52 + (i.val - 52) = i.val by omega] at hm
  change movesGrid.intervals[i.val]? = detailEarly.intervals[i.val - 52]? at hm
  rw [List.getElem?_eq_getElem (show i.val < movesGrid.intervals.length by
      rw [movesGrid_length]; exact i.isLt),
    List.getElem?_eq_getElem (show i.val - 52 < detailEarly.intervals.length by
      rw [detailEarly_length]; omega)] at hm
  exact Option.some.inj hm

set_option maxRecDepth 10000 in
theorem old_row_coordinates {r : GridReplacement} (hr : r ∈ fiveReplacements) :
    let L := gridInterval movesGrid movesGrid_length (leftMoveIndex r hr)
    let R := gridInterval movesGrid movesGrid_length (rightMoveIndex r hr)
    (L.fst = r.lower ∧ L.snd = r.original) ∧ (R.fst = r.original ∧ R.snd = r.upper) := by
  have hbounds := idx_bounds hr
  have hleft := middle_index (i := leftMoveIndex r hr)
    (by change 52 ≤ r.site - 1; omega) (by change r.site - 1 < 452; omega)
  have hright := middle_index (i := rightMoveIndex r hr)
    (by change 52 ≤ r.site; omega) (by change r.site < 452; omega)
  dsimp only
  rw [hleft, hright]
  simp only [fiveReplacements, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor <;> constructor
  all_goals
    change Enclosure.sfrac false _ _ = _
    norm_num [Enclosure.sfrac]

theorem uniqueInMovesRow (i : Fin 10156) {t : ℝ}
    (ht : t ∈ Ioo (gridInterval movesGrid movesGrid_length i).fst
      (gridInterval movesGrid movesGrid_length i).snd) (hz : riemannZeta (linePoint t) = 0) :
    t = movesAtlas.root i := by
  have hI : gridInterval movesGrid movesGrid_length i ∈ movesGrid.intervals :=
    List.get_mem _ _
  refine unique_in_ordered_row (atlas := movesAtlas) (i := i)
    (movesGrid.fst_nonneg _ hI) ((movesGrid.le_height hI).trans movesGrid_below)
    ?_ ?_ ht hz
  · intro j hj
    exact ((gridRoot_spec movesGrid movesGrid_length j).1.2.trans_le
      (grid_separated movesGrid movesGrid_length j i hj)).le
  · intro j hj
    exact ((grid_separated movesGrid movesGrid_length i j hj).trans_lt
      (gridRoot_spec movesGrid movesGrid_length j).1.1).le

/-- Each of the five actual new boundaries preserves the two exact original zero indices
    adjacent to that site. All other sites agree definitionally with the old grid. -/
theorem actual_five_replacements_preserve_indexed_roots {r : GridReplacement}
    (hr : r ∈ fiveReplacements) :
    originalAtlas.root (leftMoveIndex r hr) ∈ Ioo r.lower r.moved ∧
      originalAtlas.root (rightMoveIndex r hr) ∈ Ioo r.moved r.upper := by
  rw [← independent_assembly_same_root]
  obtain ⟨⟨hL, hM₀⟩, ⟨hM₁, hR⟩⟩ := old_row_coordinates hr
  obtain ⟨signL, signM, signR⟩ := fiveReplacements_trueSigns hr
  apply fiveReplacements_preserve_roots hr _ _ _ _ signL signM signR
  · rw [moves_root_eq, ← hL, ← hM₀]
    exact (gridRoot_spec movesGrid movesGrid_length (leftMoveIndex r hr)).1
  · rw [moves_root_eq, ← hM₁, ← hR]
    exact (gridRoot_spec movesGrid movesGrid_length (rightMoveIndex r hr)).1
  · intro t ht hz
    exact uniqueInMovesRow _ (by simpa only [hL, hM₀] using ht) hz
  · intro t ht hz
    exact uniqueInMovesRow _ (by simpa only [hM₁, hR] using ht) hz

#print axioms actual_five_replacements_preserve_indexed_roots

end ZetaSourceRows

end
