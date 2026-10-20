/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Cancellation of local complete intersection against smooth postcomposition

If a composite morphism of algebraic spaces is a local complete intersection
and the second factor is smooth, then the first factor is a local complete
intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsLocalCompleteIntersection

/-- If a composite morphism of algebraic spaces is a local complete intersection
and the second factor is smooth, then the first factor is a local complete
intersection. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Smooth g] [IsLocalCompleteIntersection (f ≫ g)] :
    IsLocalCompleteIntersection f :=
  sorry

/-- Local complete intersection morphisms of algebraic spaces cancel against a
smooth postcomposition. -/
instance instHasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicSpace
