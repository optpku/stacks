module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Sites.Over.Adjunction

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Pullback along a scheme morphism is continuous between the big sites
for any standard topology. -/
instance pullback_isContinuous (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (τ.overTopology Y) (τ.overTopology X) := sorry

end AlgebraicGeometry.StandardTopology.Big
