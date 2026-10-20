/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Smooth surjective atlases of quotient stacks

The canonical atlas of the quotient stack of a smooth groupoid in algebraic spaces
is smooth and surjective.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

/-- The canonical morphism from the object-space fibration of a smooth groupoid
in algebraic spaces to its quotient stack is smooth and surjective. -/
theorem smooth_surjective_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (hG : GroupoidAlgebraicSpace.Smooth G) :
    Groupoids.Hom.Smooth (atlas G) ∧ Groupoids.Hom.Surjective (atlas G) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
