/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.ToPresheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence.QuasiInverse
public import ReasLib.CategoryTheory.Fibered.InSets.LocalDiscreteness

/-!
# Discrete Grothendieck correspondence

Set-valued presheaves give discrete fibrations through categories of elements.
Conversely, a discrete fibration determines its choice-independent presheaf of
fiber objects. These constructions form an equivalence with categories fibred
in sets.

This is the compatibility aggregate. The reusable layers are separated by
responsibility: `OfPresheaf` contains the discrete Grothendieck construction,
`FiberObject` constructs and reconstructs fiber-object presheaves,
`ToPresheaf` packages straightening, and `Equivalence` contains the two
quasi-inverse comparisons. `Equivalence.QuasiInverse` packages those
comparisons as specified `Functor.QuasiInverse` and `≌` owners. Local
discreteness belongs independently to the
`InSets` hierarchy.

For a `Type`-valued presheaf, mathlib's `Functor.Elements`,
`CategoryOfElements.map`, and `CategoryOfElements.π` are the canonical
category-of-elements owners. The converse `Functor.fiberObjectPresheaf` uses
the intrinsic reindexing determined by unique lifting, so it does not expose a
noncanonical cleavage in its primary computation API.
-/
