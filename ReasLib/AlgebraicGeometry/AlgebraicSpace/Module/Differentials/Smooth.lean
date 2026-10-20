module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative differential sheaf of a smooth morphism of algebraic spaces over a scheme
is a finite locally free module on the small étale site of the source. -/
@[stacks 0CK5]
instance isFiniteLocallyFree_relativeDifferentials_of_smooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Smooth f] :
    (Ω[f]).IsFiniteLocallyFree :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
