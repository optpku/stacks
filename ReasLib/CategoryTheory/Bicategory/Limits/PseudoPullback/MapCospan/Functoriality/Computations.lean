/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Identity.Projections
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Composition.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Composition.Projections

/-!
# Computations for functorial universal pseudopullback maps

Compatibility aggregate for the identity and composition coherence of
`PseudoPullbackCone.mapCospan.functor`. It exposes the readable coherence
isomorphisms together with their cell and projection formulas, while the core
functor remains owned by `MapCospan.Functoriality`.

Import the focused identity or composition leaf when only one coherence layer
is needed. This path is the complete computation entry point for downstream
uses of functorial universal pseudopullback maps.
-/
