/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Thickenings of algebraic spaces

A morphism of algebraic spaces is a thickening when every represented scheme
pullback is a surjective closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is a thickening when every represented scheme pullback is a
surjective closed immersion. -/
def thickening {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) := fun _ _ f =>
  (MorphismProperty.over
    ((@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}))).presheaf f

/-- The composite of two thickenings of algebraic spaces is a thickening. -/
theorem thickening_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : thickening f) (hg : thickening g) :
    thickening (f ≫ g) := sorry

/-- The property of being a thickening of algebraic spaces is stable under composition. -/
instance thickening_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (thickening : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace
