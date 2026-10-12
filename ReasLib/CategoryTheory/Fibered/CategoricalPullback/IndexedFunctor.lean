/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Explicit
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Chosen
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Coherence
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Hom

/-!
# Indexed fiber equivalence for a categorical pullback

Compatibility aggregate for the indexed pullback-fiber comparison API.
The canonical declarations are organized below
`CategoricalPullback.Indexed.{explicit,chosen,canonical}`; the last owner
further separates functor, restriction comparison, coherence, and hom
transport. Focused clients can import the corresponding leaf.

The compatibility path deliberately has no declarations of its own.
-/
