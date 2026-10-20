/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of local finite type against arbitrary postcomposition

If a composite morphism of algebraic spaces is locally of finite type, then so
is the first factor. No hypothesis is imposed on the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- If a composite morphism of algebraic spaces is locally of finite type, then
so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f := sorry

end LocallyOfFiniteType

/-- Locally of finite type morphisms of algebraic spaces cancel against an
arbitrary postcomposition. -/
instance locallyOfFiniteType_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

end AlgebraicGeometry.AlgebraicSpace
