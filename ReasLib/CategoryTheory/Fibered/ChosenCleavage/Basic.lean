/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Composition
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence

@[expose] public section

/-!
# Choice-specialized reindexing

Compatibility aggregate for the selected-cleavage reindexing API. Focused
consumers can import `Basic.Core`, `Basic.Composition`, or `Basic.Coherence`.
The core data and factorization computations are grouped under
`Functor.Chosen`, with direct owners such as `reindex`, `cartesianHom`,
`cartesianFactor`, and `verticalFactor`.
-/
