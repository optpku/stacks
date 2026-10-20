module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.Unramified

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Etale

/-- A flat, locally finitely presented, unramified morphism of groupoid fibrations
representable by algebraic spaces is étale. -/
theorem of_unramified {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_unramified : has (@AlgebraicSpace.Unramified S) f) : Etale f :=
  sorry

end Etale

end AlgebraicGeometry.Groupoids.Hom
