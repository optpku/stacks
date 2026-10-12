/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Properties

/-!
# Reindexing directed algebra approximations

Aggregate import for the reindexing API.  Core data, colimit transport,
base-change computations, and optional property transport are separate leaves.
-/

@[expose] public section

/- The declarations live in `Reindex.Core`, `Reindex.Colimit`,
`Reindex.BaseChange`, and `Reindex.Properties`; this file is the stable
aggregate import. -/
