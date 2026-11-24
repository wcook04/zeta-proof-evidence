module

public import SourceAtlasAdapter
public import DetailedBatch12
public import OpaquePrefix
public import OriginalOpaqueSuffix
public import Zeta.Gram.Certificates

@[expose] public section


open Set Zeta.Certificates Zeta.Certificates.Gram

noncomputable section

namespace ZetaSourceRows

abbrev prefixSpec := opaquePrefix
abbrev prefixRows := prefixSpec.bundle
abbrev suffixRows := opaqueSuffix.bundle

def throughBatch12 : CertifiedZeroIntervals :=
  prefixRows.append detailedBatch12 (separated_of_endpoints
    prefixSpec.bundle_getLast? detailedBatch12_head le_rfl)

theorem throughBatch12_last : throughBatch12.intervals.getLast?.map (·.snd) =
    some (Enclosure.sfrac false 2983035 1000) := by
  have hn : detailedBatch12.intervals ≠ [] := by
    intro h
    have hc := detailedBatch12_length
    rw [h] at hc
    contradiction
  unfold throughBatch12
  exact (congrArg (Option.map (·.snd))
    (CertifiedZeroIntervals.append_getLast? _ _ _ hn)).trans detailedBatch12_last

/-- Only the 200 rows of batch 12 are explicit in this list. All other endpoint
    proofs and individual rows stay behind upstream `BatchSpec` declarations. -/
def originalGrid : CertifiedZeroIntervals :=
  throughBatch12.append suffixRows (separated_of_endpoints
    throughBatch12_last opaqueSuffix.bundle_head? le_rfl)

theorem originalGrid_length : originalGrid.intervals.length = 10156 := by
  simp [originalGrid, throughBatch12]

private theorem originalGrid_last : originalGrid.intervals.getLast?.map (·.snd) =
    some (Enclosure.sfrac false 10011107 1000) := by
  unfold originalGrid
  exact (congrArg (Option.map (·.snd))
    (CertifiedZeroIntervals.append_getLast? _ _ _ opaqueSuffix.bundle_ne)).trans
    opaqueSuffix.bundle_getLast?

theorem originalGrid_below : originalGrid.height ≤ gramPoint certifiedGramBlockSeq.minIdx := by
  refine originalGrid.height_le_of_getLast?_snd originalGrid_last ?_
  exact (show Enclosure.sfrac false 10011107 1000 ≤ gp1.fst by
    norm_num [Enclosure.sfrac]).trans certifiedGramBlockSeq.head_left_le_gramPoint

/-- Mercuri’s original small-height Gram certificate, paired with the reconstructed grid. -/
def originalCount : CertifiedZeroCount where
  toCertifiedGramBlockSeq := certifiedGramBlockSeq
  toCertifiedZeroIntervals := originalGrid
  count := by rw [originalGrid_length]; decide
  below := originalGrid_below

private theorem rightEdge_below_count : rightEdge < gramPoint originalCount.minIdx :=
  (show rightEdge < gp1.fst by norm_num [rightEdge]).trans
    (GramPoint.certificate_left_lt_gramPoint gp1_cert)

private theorem grid_middle_row {j : ℕ} (hj : j < 200) :
    originalGrid.intervals[2252 + j]? = detailedBatch12.intervals[j]? := by
  change ((prefixRows.intervals ++ detailedBatch12.intervals) ++ suffixRows.intervals)[2252 + j]? =
    detailedBatch12.intervals[j]?
  have hm := getElem?_middle prefixRows.intervals detailedBatch12.intervals suffixRows.intervals
    (show j < detailedBatch12.intervals.length by simpa using hj)
  simpa using hm

private theorem row2391_eq : gridInterval originalGrid originalGrid_length idx2391 =
    detailedBatch12.intervals[138]'(by rw [detailedBatch12_length]; decide) := by
  apply Option.some.inj
  have h := grid_middle_row (j := 138) (by decide)
  rw [List.getElem?_eq_getElem (show 2252 + 138 < originalGrid.intervals.length by
      rw [originalGrid_length]; decide),
    List.getElem?_eq_getElem (show 138 < detailedBatch12.intervals.length by
      rw [detailedBatch12_length]; decide)] at h
  exact h

private theorem row2392_eq : gridInterval originalGrid originalGrid_length idx2392 =
    detailedBatch12.intervals[139]'(by rw [detailedBatch12_length]; decide) := by
  apply Option.some.inj
  have h := grid_middle_row (j := 139) (by decide)
  rw [List.getElem?_eq_getElem (show 2252 + 139 < originalGrid.intervals.length by
      rw [originalGrid_length]; decide),
    List.getElem?_eq_getElem (show 139 < detailedBatch12.intervals.length by
      rw [detailedBatch12_length]; decide)] at h
  exact h

def originalAtlas : Atlas (gramPoint originalCount.minIdx) :=
  fromMercuriCount originalCount originalGrid_length originalGrid originalGrid_length
    originalGrid_below

theorem originalPlacement : PairPlacement originalAtlas := by
  apply placement_fromMercuriCount originalCount originalGrid_length originalGrid
    originalGrid_length originalGrid_below
  · rw [row2391_eq]; exact detailedBatch12_row138.1
  · rw [row2391_eq]; exact detailedBatch12_row138.2
  · rw [row2392_eq]; exact detailedBatch12_row139.1
  · rw [row2392_eq]; exact detailedBatch12_row139.2

/-- The count reconstructed from the pinned local Gram certificate also proves RH up to
    the cutoff used in the original short-height release. -/
theorem reconstructedRH10011 : RiemannHypothesisUpTo 10011 := by
  refine (riemannHypothesisUpTo originalCount).mono ?_
  exact (show (10011 : ℝ) ≤ gp1.fst by norm_num).trans
    (GramPoint.certificate_left_lt_gramPoint gp1_cert).le

theorem originalCount_height_ge_10000 : (10000 : ℝ) ≤ gramPoint originalCount.minIdx :=
  (show (10000 : ℝ) ≤ gp1.fst by norm_num).trans
    (GramPoint.certificate_left_lt_gramPoint gp1_cert).le

/-- The two original numerical intervals correspond to the specified ordinals in the
    complete ordered atlas. The indices are zero-based in Lean and positive ordinals in prose. -/
theorem original_pair_ordinals : originalAtlas.root idx2391 ∈ boxLeft ∧
    originalAtlas.root idx2392 ∈ boxRight :=
  ⟨originalPlacement.lower, originalPlacement.upper⟩

/-- The exact original pair source rows isolate the 2,391st and 2,392nd simple zeros. -/
theorem original_pair_unique :
    (∃! a, a ∈ boxLeft ∧ riemannZeta (linePoint a) = 0) ∧
    (∃! b, b ∈ boxRight ∧ riemannZeta (linePoint b) = 0) :=
  unique_rows originalPlacement rightEdge_below_count

theorem original_pair_simple (i : Fin 10156) :
    meromorphicOrderAt riemannZeta (linePoint (originalAtlas.root i)) = 1 :=
  riemannZeta.meromorphicOrderAt_eq_one_upto originalCount
    (by simpa using originalAtlas.inRegion i) (originalAtlas.vanishes i)

/-- A zeta zero whose ordinate differs from the two selected original roots is
    outside the exact coarse span. The hypotheses identify no preferred product or score. -/
theorem original_pair_exterior {z : ℂ} (hz : riemannZeta z = 0)
    (hneA : z.im ≠ originalAtlas.root idx2391) (hneB : z.im ≠ originalAtlas.root idx2392) :
    z.im ≤ leftEdge ∨ rightEdge ≤ z.im :=
  exterior_of_atlas originalPlacement rightEdge_below_count hz hneA hneB

#print axioms reconstructedRH10011
#print axioms original_pair_ordinals
#print axioms original_pair_unique
#print axioms original_pair_simple
#print axioms original_pair_exterior

end ZetaSourceRows

end
