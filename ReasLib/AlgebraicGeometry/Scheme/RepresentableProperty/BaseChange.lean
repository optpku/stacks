module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.representableMorphismProperty

/-- A representable morphism with a base-change-stable, fppf-local property of
scheme morphisms retains that property after arbitrary base change. -/
theorem pullback_fst {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : H ⟶ G) [HasPullback b a]
    (ha : representableMorphismProperty S P a) :
    representableMorphismProperty S P (pullback.fst b a) := sorry

end AlgebraicGeometry.Scheme.representableMorphismProperty
