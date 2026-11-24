# Zeta proof evidence

This snapshot supplies the Lean sources and saved Comparator checks for Will
Cook’s *Shared Riemann–Siegel bounds and a Lehmer pair from seven values*.

- [Lean declarations](declarations.md) links to the exact source lines for the paper's results.
- [Comparator records](verification.md) links to the 20 saved runs, their Challenge statements, and their receipts and logs.
- [Named Lehmer-pair comparison](verification.md#the-lehmer-pair) identifies the checks for the named result.

The Lean source uses the [Mercuri–Mehta catalogue revision](https://github.com/smmercuri/zeta/tree/34037d5a7662e2eb6e970bfb22299c84e45ed5d9).
The table for the later catalogue uses [revision c06b4e13d9](https://github.com/smmercuri/zeta/tree/c06b4e13d9c847e50a32c3d738271cbad62ae9f3).
The saved checks used [Comparator for Lean 4.35.0](https://github.com/leanprover/comparator/tree/v4.35.0).

From a checkout of this snapshot, verify the evidence files with

~~~sh
shasum -a 256 -c SHA256SUMS
~~~

The source files are the indexed excerpts from the proof development.
The complete build prerequisites and numerical replay are described in
the paper's companion archive. The log and receipt files document the
saved Comparator runs.

| Location | Contents |
| --- | --- |
| [sources/lean/](sources/lean/) | Exact copies of the indexed Lean files |
| [sources/claim-index.tsv](sources/claim-index.tsv) | Declaration names, source lines and upstream revisions. The file column uses paths from the companion ZIP. |
| [evidence/comparator/](evidence/comparator/) | Frozen Challenge files, configurations, receipts and logs |
| [licenses/](licenses/) | Retained upstream license |

Corrections to a source coordinate or a record link can be filed as a
GitHub issue. See [NOTICE](NOTICE) for attribution.
