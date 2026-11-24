# Comparator records

The saved records cover 140 accepted target checks across 20 local Comparator runs.
Targets repeat across some runs. The default Lean kernel accepted the
listed checks in Lean 4.35.0 with sandboxing disabled.
Follow a checked name to its frozen Challenge statement.
Each run also retains the configuration, receipt and kernel log.

## By result

### The Lehmer pair

- [`ZetaComparator.pairClassical`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L33-L40) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.pairStrict`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L19-L23) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.pairLehmer`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L26-L30) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).

### The coefficient bound

- [`ZetaComparator.abs_correctionLinear_lt_decimal`](evidence/comparator/grid-coefficient-r1/fixtures/Challenge.lean#L15-L16) in [`grid-coefficient-r1`](#grid-coefficient-r1).
- [`ZetaComparator.abs_correctionLinear_lt_eighth`](evidence/comparator/grid-coefficient-r1/fixtures/Challenge.lean#L11-L12) in [`grid-coefficient-r1`](#grid-coefficient-r1).

### The five grid moves

- [`ZetaComparator.actual_five_replacements_preserve_indexed_roots`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L13-L16) in [`grid-moved-roots-fast`](#grid-moved-roots-fast).
- [`ZetaComparator.pinned_shared_checked`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L18-L20) in [`grid-original-full-r1`](#grid-original-full-r1).
- [`ZetaComparator.pinned_own_checked`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L23-L25) in [`grid-original-full-r1`](#grid-original-full-r1).
- [`ZetaComparator.pinned_row_count`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L11-L11) in [`grid-original-full-r1`](#grid-original-full-r1).
- [`ZetaComparator.shared_check_count`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L31-L31) in [`grid-original-full-r1`](#grid-original-full-r1).
- [`ZetaComparator.fiveReplacements_trueSigns`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L19-L20) in [`grid-moved-roots-fast`](#grid-moved-roots-fast).

### The classical normalization

- [`ZetaComparator.classicalRootArgument`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L43-L43) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.classicalArgumentRoot`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L46-L46) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.classicalNormalizedValue`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L49-L49) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.classicalNormalizedOrder`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L52-L53) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).

### Enlarged logarithmic intervals

- [`ZetaComparator.pairAbsoluteRobust`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L65-L71) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).
- [`ZetaComparator.pairRelativeRobust`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L56-L62) in [`pair-restored-shared-imports-r1`](#pair-restored-shared-imports-r1).

### The later catalogue

- [`ZetaComparator.original_classification`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L17-L17) in [`grid-later-prefix-r1`](#grid-later-prefix-r1).
- [`ZetaComparator.original_reversed_sites`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L20-L21) in [`grid-later-prefix-r1`](#grid-later-prefix-r1).
- [`ZetaComparator.moved_all_checks`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L24-L24) in [`grid-later-prefix-r1`](#grid-later-prefix-r1).
- [`ZetaComparator.moved_all_forward`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L27-L27) in [`grid-later-prefix-r1`](#grid-later-prefix-r1).

### Batch certificate checks

These runs check saved batch certificate statements. The benchmark measurements
in the paper come from the separate generator and compiler records.

- [benchmark-timing-eighth-moved-fast](#benchmark-timing-eighth-moved-fast)
- [benchmark-timing-eighth-original-fast](#benchmark-timing-eighth-original-fast)
- [benchmark-timing-stock-fast](#benchmark-timing-stock-fast)
- [benchmark-trace-eighth-moved-fast](#benchmark-trace-eighth-moved-fast)
- [benchmark-trace-eighth-original-fast](#benchmark-trace-eighth-original-fast)
- [benchmark-trace-stock](#benchmark-trace-stock)
- [benchmark-trace-stock-moved-fast](#benchmark-trace-stock-moved-fast)

## Run records

### benchmark-timing-eighth-moved-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-timing-eighth-moved-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-timing-eighth-moved-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-timing-eighth-moved-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-timing-eighth-moved-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-timing-eighth-moved-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-timing-eighth-moved-fast/fixtures/Challenge.lean#L7-L7)

### benchmark-timing-eighth-original-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-timing-eighth-original-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-timing-eighth-original-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-timing-eighth-original-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-timing-eighth-original-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-timing-eighth-original-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-timing-eighth-original-fast/fixtures/Challenge.lean#L7-L7)

### benchmark-timing-stock-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-timing-stock-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-timing-stock-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-timing-stock-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-timing-stock-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-timing-stock-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-timing-stock-fast/fixtures/Challenge.lean#L7-L7)

### benchmark-trace-eighth-moved-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-trace-eighth-moved-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-trace-eighth-moved-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-trace-eighth-moved-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-trace-eighth-moved-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-trace-eighth-moved-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-trace-eighth-moved-fast/fixtures/Challenge.lean#L7-L7)

### benchmark-trace-eighth-original-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-trace-eighth-original-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-trace-eighth-original-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-trace-eighth-original-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-trace-eighth-original-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-trace-eighth-original-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-trace-eighth-original-fast/fixtures/Challenge.lean#L7-L7)

### benchmark-trace-stock

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-trace-stock/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-trace-stock/receipt.json) · [Kernel log](evidence/comparator/benchmark-trace-stock/comparator.log) · [Configuration](evidence/comparator/benchmark-trace-stock/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-trace-stock/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-trace-stock/fixtures/Challenge.lean#L7-L7)

### benchmark-trace-stock-moved-fast

2 accepted target checks.

[Challenge](evidence/comparator/benchmark-trace-stock-moved-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/benchmark-trace-stock-moved-fast/receipt.json) · [Kernel log](evidence/comparator/benchmark-trace-stock-moved-fast/comparator.log) · [Configuration](evidence/comparator/benchmark-trace-stock-moved-fast/comparator.json)

- [`BenchmarkComparator.Batch0001`](evidence/comparator/benchmark-trace-stock-moved-fast/fixtures/Challenge.lean#L5-L5)
- [`BenchmarkComparator.Batch0002`](evidence/comparator/benchmark-trace-stock-moved-fast/fixtures/Challenge.lean#L7-L7)

### grid-coefficient-r1

2 accepted target checks.

[Challenge](evidence/comparator/grid-coefficient-r1/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-coefficient-r1/receipt.json) · [Kernel log](evidence/comparator/grid-coefficient-r1/comparator.log) · [Configuration](evidence/comparator/grid-coefficient-r1/comparator.json) · [Source map](evidence/comparator/grid-coefficient-r1/fixtures/source-map.tsv)

- [`ZetaComparator.abs_correctionLinear_lt_eighth`](evidence/comparator/grid-coefficient-r1/fixtures/Challenge.lean#L11-L12)
- [`ZetaComparator.abs_correctionLinear_lt_decimal`](evidence/comparator/grid-coefficient-r1/fixtures/Challenge.lean#L15-L16)

### grid-focused-r2

57 accepted target checks.

[Challenge](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-focused-r2/receipt.json) · [Kernel log](evidence/comparator/grid-focused-r2/comparator.log) · [Configuration](evidence/comparator/grid-focused-r2/comparator.json)

- [`ZetaComparator.moved_shared_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L14-L16)
- [`ZetaComparator.original_shared_failure_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L19-L21)
- [`ZetaComparator.moved_legacy_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L24-L26)
- [`ZetaComparator.original_own_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L29-L31)
- [`ZetaComparator.moved_shared_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L34-L36)
- [`ZetaComparator.original_shared_failure_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L39-L41)
- [`ZetaComparator.moved_legacy_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L44-L46)
- [`ZetaComparator.original_own_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L49-L51)
- [`ZetaComparator.moved_shared_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L54-L56)
- [`ZetaComparator.original_shared_failure_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L59-L61)
- [`ZetaComparator.moved_legacy_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L64-L66)
- [`ZetaComparator.original_own_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L69-L71)
- [`ZetaComparator.moved_shared_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L74-L76)
- [`ZetaComparator.original_shared_failure_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L79-L81)
- [`ZetaComparator.moved_legacy_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L84-L86)
- [`ZetaComparator.original_own_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L89-L91)
- [`ZetaComparator.moved_shared_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L94-L96)
- [`ZetaComparator.original_shared_failure_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L99-L101)
- [`ZetaComparator.moved_legacy_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L104-L106)
- [`ZetaComparator.original_own_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L109-L111)
- [`ZetaComparator.moved_own_3823`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L114-L116)
- [`ZetaComparator.original_own_failure_3823`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L119-L121)
- [`ZetaComparator.runner_up_pass_4765`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L124-L126)
- [`ZetaComparator.runner_up_fail_4765`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L129-L131)
- [`ZetaComparator.moved_count`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L134-L134)
- [`ZetaComparator.moved_checks`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L137-L137)
- [`ZetaComparator.moved_checked`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L140-L140)
- [`ZetaComparator.hardyZ_moved_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L143-L143)
- [`ZetaComparator.hardyZ_moved_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L146-L146)
- [`ZetaComparator.hardyZ_moved_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L149-L149)
- [`ZetaComparator.hardyZ_moved_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L152-L152)
- [`ZetaComparator.hardyZ_moved_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L155-L155)
- [`ZetaComparator.all_moved_negative`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L158-L159)
- [`ZetaComparator.hardyZ_left_neighbor_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L162-L162)
- [`ZetaComparator.hardyZ_right_neighbor_106`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L165-L165)
- [`ZetaComparator.hardyZ_left_neighbor_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L168-L168)
- [`ZetaComparator.hardyZ_right_neighbor_114`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L171-L171)
- [`ZetaComparator.hardyZ_left_neighbor_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L174-L174)
- [`ZetaComparator.hardyZ_right_neighbor_184`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L177-L177)
- [`ZetaComparator.hardyZ_left_neighbor_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L180-L180)
- [`ZetaComparator.hardyZ_right_neighbor_242`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L183-L183)
- [`ZetaComparator.hardyZ_left_neighbor_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L186-L186)
- [`ZetaComparator.hardyZ_right_neighbor_378`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L189-L189)
- [`ZetaComparator.fiveForcedSites_card`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L192-L192)
- [`ZetaComparator.original_forcedSite_fails`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L195-L196)
- [`ZetaComparator.replacement_forcedSite_passes`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L199-L200)
- [`ZetaComparator.five_forcedSites_must_move`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L203-L206)
- [`ZetaComparator.five_le_card_moves_of_fixed_shared_pass`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L209-L212)
- [`ZetaComparator.original_forcedSite_passes_own`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L215-L217)
- [`ZetaComparator.hardyZ_original_forcedSites_neg`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L220-L223)
- [`ZetaComparator.hardyZ_replacement_forcedSites_neg`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L226-L229)
- [`ZetaComparator.fiveForcedSites_hardyZ_neg`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L232-L234)
- [`ZetaComparator.ownHeight_oneMove_optimal_of_separators`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L237-L256)
- [`ZetaComparator.threeForcedSites_card`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L259-L259)
- [`ZetaComparator.original_shared_strictFailure_at_any_nonneg_coefficient`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L262-L265)
- [`ZetaComparator.three_forcedSites_must_move_for_any_nonnegative_coefficient`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L268-L273)
- [`ZetaComparator.three_le_card_moves_for_any_nonnegative_coefficient`](evidence/comparator/grid-focused-r2/fixtures/Challenge.lean#L276-L281)

### grid-later-prefix-r1

6 accepted target checks.

[Challenge](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-later-prefix-r1/receipt.json) · [Kernel log](evidence/comparator/grid-later-prefix-r1/comparator.log) · [Configuration](evidence/comparator/grid-later-prefix-r1/comparator.json) · [Source map](evidence/comparator/grid-later-prefix-r1/fixtures/source-map.tsv)

- [`ZetaComparator.original_count`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L11-L11)
- [`ZetaComparator.moved_count`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L14-L14)
- [`ZetaComparator.original_classification`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L17-L17)
- [`ZetaComparator.original_reversed_sites`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L20-L21)
- [`ZetaComparator.moved_all_checks`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L24-L24)
- [`ZetaComparator.moved_all_forward`](evidence/comparator/grid-later-prefix-r1/fixtures/Challenge.lean#L27-L27)

### grid-moved-roots-fast

18 accepted target checks.

[Challenge](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-moved-roots-fast/receipt.json) · [Kernel log](evidence/comparator/grid-moved-roots-fast/comparator.log) · [Configuration](evidence/comparator/grid-moved-roots-fast/comparator.json) · [Source map](evidence/comparator/grid-moved-roots-fast/fixtures/source-map.tsv)

- [`ZetaComparator.actual_five_replacements_preserve_indexed_roots`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L13-L16)
- [`ZetaComparator.fiveReplacements_trueSigns`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L19-L20)
- [`ZetaComparator.independent_assembly_same_root`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L23-L23)
- [`ZetaComparator.hardyZ_moved_106`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L26-L26)
- [`ZetaComparator.hardyZ_left_neighbor_106`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L29-L29)
- [`ZetaComparator.hardyZ_right_neighbor_106`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L32-L32)
- [`ZetaComparator.hardyZ_moved_114`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L35-L35)
- [`ZetaComparator.hardyZ_left_neighbor_114`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L38-L38)
- [`ZetaComparator.hardyZ_right_neighbor_114`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L41-L41)
- [`ZetaComparator.hardyZ_moved_184`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L44-L44)
- [`ZetaComparator.hardyZ_left_neighbor_184`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L47-L47)
- [`ZetaComparator.hardyZ_right_neighbor_184`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L50-L50)
- [`ZetaComparator.hardyZ_moved_242`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L53-L53)
- [`ZetaComparator.hardyZ_left_neighbor_242`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L56-L56)
- [`ZetaComparator.hardyZ_right_neighbor_242`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L59-L59)
- [`ZetaComparator.hardyZ_moved_378`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L62-L62)
- [`ZetaComparator.hardyZ_left_neighbor_378`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L65-L65)
- [`ZetaComparator.hardyZ_right_neighbor_378`](evidence/comparator/grid-moved-roots-fast/fixtures/Challenge.lean#L68-L68)

### grid-original-full-r1

7 accepted target checks.

[Challenge](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-original-full-r1/receipt.json) · [Kernel log](evidence/comparator/grid-original-full-r1/comparator.log) · [Configuration](evidence/comparator/grid-original-full-r1/comparator.json) · [Source map](evidence/comparator/grid-original-full-r1/fixtures/source-map.tsv)

- [`ZetaComparator.pinned_row_count`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L11-L11)
- [`ZetaComparator.pinnedRows_recover_sharedBatches`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L14-L15)
- [`ZetaComparator.pinned_shared_checked`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L18-L20)
- [`ZetaComparator.pinned_own_checked`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L23-L25)
- [`ZetaComparator.shared_checked`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L28-L28)
- [`ZetaComparator.shared_check_count`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L31-L31)
- [`ZetaComparator.shared_batched_checks`](evidence/comparator/grid-original-full-r1/fixtures/Challenge.lean#L34-L34)

### grid-original-prefix-r1

5 accepted target checks.

[Challenge](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-original-prefix-r1/receipt.json) · [Kernel log](evidence/comparator/grid-original-prefix-r1/comparator.log) · [Configuration](evidence/comparator/grid-original-prefix-r1/comparator.json)

- [`ZetaComparator.pinned_row_count`](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean#L11-L11)
- [`ZetaComparator.pinnedRows_recover_sharedBatches`](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean#L14-L15)
- [`ZetaComparator.pinned_shared_checked`](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean#L18-L20)
- [`ZetaComparator.pinned_own_checked`](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean#L23-L25)
- [`ZetaComparator.shared_checked`](evidence/comparator/grid-original-prefix-r1/fixtures/Challenge.lean#L28-L28)

### grid-transport-r1

5 accepted target checks.

[Challenge](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean) · [Receipt](evidence/comparator/grid-transport-r1/receipt.json) · [Kernel log](evidence/comparator/grid-transport-r1/comparator.log) · [Configuration](evidence/comparator/grid-transport-r1/comparator.json)

- [`ZetaComparator.abs_correctionLinear_le_of_third_deriv`](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean#L11-L13)
- [`ZetaComparator.abs_hardyZRemainderRS₀_le_with`](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean#L16-L19)
- [`ZetaComparator.hardyZSign_of_own_signedMargin`](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean#L22-L26)
- [`ZetaComparator.hardyZSign_of_signedMargin`](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean#L29-L34)
- [`ZetaComparator.abs_hardyZRemainderRS₀_le_eighth`](evidence/comparator/grid-transport-r1/fixtures/Challenge.lean#L37-L38)

### pair-absolute

2 accepted target checks.

[Challenge](evidence/comparator/pair-absolute/fixtures/Challenge.lean) · [Receipt](evidence/comparator/pair-absolute/receipt.json) · [Kernel log](evidence/comparator/pair-absolute/comparator.log) · [Configuration](evidence/comparator/pair-absolute/comparator.json)

- [`ZetaComparatorComponents.component_widenedPairObservation_le`](evidence/comparator/pair-absolute/fixtures/Challenge.lean#L11-L15)
- [`ZetaComparatorComponents.component_xi_pair_absolute`](evidence/comparator/pair-absolute/fixtures/Challenge.lean#L18-L22)

### pair-csv

7 accepted target checks.

[Challenge](evidence/comparator/pair-csv/fixtures/Challenge.lean) · [Receipt](evidence/comparator/pair-csv/receipt.json) · [Kernel log](evidence/comparator/pair-csv/comparator.log) · [Configuration](evidence/comparator/pair-csv/comparator.json)

- [`ZetaComparatorComponents.component_h₀Argument_scaledRoot`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L14-L14)
- [`ZetaComparatorComponents.component_scaledRoot_h₀Argument`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L17-L17)
- [`ZetaComparatorComponents.component_csvH₀_at_scaledRoot`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L20-L20)
- [`ZetaComparatorComponents.component_csvH₀_order`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L23-L24)
- [`ZetaComparatorComponents.component_h₀Term_eq_complexTerm`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L27-L27)
- [`ZetaComparatorComponents.component_complexScore_comparison`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L30-L37)
- [`ZetaComparatorComponents.component_im_tsum_exterior_eq_zero_of_reflection`](evidence/comparator/pair-csv/fixtures/Challenge.lean#L40-L42)

### pair-csv-bound

1 accepted target checks.

[Challenge](evidence/comparator/pair-csv-bound/fixtures/Challenge.lean) · [Receipt](evidence/comparator/pair-csv-bound/receipt.json) · [Kernel log](evidence/comparator/pair-csv-bound/comparator.log) · [Configuration](evidence/comparator/pair-csv-bound/comparator.json)

- [`ZetaComparatorComponents.component_csvScore_bound`](evidence/comparator/pair-csv-bound/fixtures/Challenge.lean#L11-L15)

### pair-ranked

1 accepted target checks.

[Challenge](evidence/comparator/pair-ranked/fixtures/Challenge.lean) · [Receipt](evidence/comparator/pair-ranked/receipt.json) · [Kernel log](evidence/comparator/pair-ranked/comparator.log) · [Configuration](evidence/comparator/pair-ranked/comparator.json)

- [`ZetaComparatorComponents.component_pair2391_of_ranked_atlas`](evidence/comparator/pair-ranked/fixtures/Challenge.lean#L11-L18)

### pair-relative

6 accepted target checks.

[Challenge](evidence/comparator/pair-relative/fixtures/Challenge.lean) · [Receipt](evidence/comparator/pair-relative/receipt.json) · [Kernel log](evidence/comparator/pair-relative/comparator.log) · [Configuration](evidence/comparator/pair-relative/comparator.json)

- [`ZetaComparatorComponents.component_logWeight_norm`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L13-L13)
- [`ZetaComparatorComponents.component_upper_perturb_logs`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L16-L19)
- [`ZetaComparatorComponents.component_weightedLogDelta_abs_le`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L22-L24)
- [`ZetaComparatorComponents.component_upper_perturb_logs_abs_le`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L27-L31)
- [`ZetaComparatorComponents.component_relative_transport_lt_robust`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L34-L35)
- [`ZetaComparatorComponents.component_robustScoreCutoff_lt`](evidence/comparator/pair-relative/fixtures/Challenge.lean#L38-L38)

### pair-restored-shared-imports-r1

9 accepted target checks.

[Challenge](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean) · [Receipt](evidence/comparator/pair-restored-shared-imports-r1/receipt.json) · [Kernel log](evidence/comparator/pair-restored-shared-imports-r1/comparator.log) · [Configuration](evidence/comparator/pair-restored-shared-imports-r1/comparator.json) · [Solution](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairSolution.lean) · [Statement mismatch control](evidence/comparator/pair-restored-shared-imports-r1/negative-control.log)

The statement-mismatch control was rejected.

- [`ZetaComparator.pairStrict`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L19-L23)
- [`ZetaComparator.pairLehmer`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L26-L30)
- [`ZetaComparator.pairClassical`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L33-L40)
- [`ZetaComparator.classicalRootArgument`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L43-L43)
- [`ZetaComparator.classicalArgumentRoot`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L46-L46)
- [`ZetaComparator.classicalNormalizedValue`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L49-L49)
- [`ZetaComparator.classicalNormalizedOrder`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L52-L53)
- [`ZetaComparator.pairRelativeRobust`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L56-L62)
- [`ZetaComparator.pairAbsoluteRobust`](evidence/comparator/pair-restored-shared-imports-r1/fixtures/PairChallenge.lean#L65-L71)
