/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Coherence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Fiberwise

/-!
# Functors between indexed categories over a base functor

A `Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor u F G` is the
universe-polymorphic component form of a pseudonatural transformation from `F`
to the pullback of `G` along `u : C ⥤ D`. Its component categories may live in
different universes, so this owner applies where bundling both sides into
mathlib's single-bicategory `StrongTrans` would force unnecessary resizing.

The naturality isomorphisms are indexed by arrows of the ordinary base
category. Identity and composition coherence are stated componentwise in `Cat`,
using the source-facing `mapIdOp` and `mapCompOp` API. For fixed base, source,
and target, indexed functors form a category under modifications; composition
is functorial in both variables and has canonical associativity and unit
comparisons.

This is the compatibility import for the basic transport API, composition and
whiskering, coherence isomorphisms, and fiberwise properties. Focused clients
should import the smallest corresponding leaf.
-/
