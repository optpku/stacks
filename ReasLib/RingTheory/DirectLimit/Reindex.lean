/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Reindex.Core
public import ReasLib.RingTheory.DirectLimit.Reindex.Equiv

/-!
# Reindexing ring direct limits

Aggregate import for the reindexing API.  Core comparison maps and equivalence
computation laws are available independently from their corresponding leaves.
-/

@[expose] public section

/- The declarations live in `Reindex.Core` and `Reindex.Equiv`; this file is
the stable aggregate import. -/
