/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Atlases of flat locally finitely presented groupoids

The canonical atlas of the quotient stack of a flat locally finitely presented
groupoid in algebraic spaces is flat, locally of finite presentation, and surjective.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

/-- The canonical atlas of the quotient stack of a flat locally finitely presented
groupoid in algebraic spaces is flat. -/
theorem flat_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (hFlat : GroupoidAlgebraicSpace.Flat G)
    (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G) :
    Groupoids.Hom.Flat (atlas G) := sorry

/-- The canonical atlas of the quotient stack of a flat locally finitely presented
groupoid in algebraic spaces is locally of finite presentation. -/
theorem locallyOfFinitePresentation_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (hFlat : GroupoidAlgebraicSpace.Flat G)
    (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G) :
    Groupoids.Hom.LocallyOfFinitePresentation (atlas G) := sorry

/-- The canonical atlas of the quotient stack of a flat locally finitely presented
groupoid in algebraic spaces is surjective. -/
theorem surjective_atlas_of_flat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (hFlat : GroupoidAlgebraicSpace.Flat G)
    (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G) :
    Groupoids.Hom.Surjective (atlas G) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
