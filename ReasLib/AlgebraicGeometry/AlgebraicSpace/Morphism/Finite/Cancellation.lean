/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of finite and integral morphisms against separated postcomposition

If a composite morphism of algebraic spaces is finite (resp. integral) and the
second factor is separated, then the first factor is finite (resp. integral).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance isFinite_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@IsFinite S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) := sorry

/-- Integral morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance isIntegralHom_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) := sorry

namespace IsFinite

/-- If a composite morphism of algebraic spaces is finite and the second factor
is separated, then the first factor is finite. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite (f ≫ g)] [Separated g] : IsFinite f :=
  MorphismProperty.of_postcomp _ f g ‹Separated g› ‹IsFinite (f ≫ g)›

end IsFinite

namespace IsIntegralHom

/-- If a composite morphism of algebraic spaces is integral and the second
factor is separated, then the first factor is integral. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegralHom (f ≫ g)] [Separated g] : IsIntegralHom f :=
  MorphismProperty.of_postcomp _ f g ‹Separated g› ‹IsIntegralHom (f ≫ g)›

end IsIntegralHom

end AlgebraicGeometry.AlgebraicSpace
