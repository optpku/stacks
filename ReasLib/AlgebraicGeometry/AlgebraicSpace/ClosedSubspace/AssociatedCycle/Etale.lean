module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import Mathlib.Algebra.Group.Indicator

/-!
# Associated cycles of étale inverse images

The associated cycle of the inverse image of an integral closed subspace under
an étale morphism has coefficient one at each irreducible component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- For an étale morphism between good algebraic spaces over a universally
catenary, absolutely quasi-separated base with a dimension function, the
associated cycle of the inverse image of an integral closed subspace, in its
relative dimension, has coefficient one at the images of all generic points of
the inverse image and zero elsewhere. -/
@[stacks 0EPY]
theorem etalePullback_integral {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX) (Z : ClosedSubspace Y)
    [IsIntegral Z.X] (ξ : genericPoints Z.X) (x : Points X) :
    ClosedSubspace.associatedCycle (Z.inverseImageSubspace f)
        (relativeDimensionFunction pX δ)
        (relativeDimensionFunction pY δ (Points.map Z.ι ξ.1)) x =
      Set.indicator
        (Points.map (Z.inverseImageSubspace f).ι '' genericPoints (Z.inverseImageSubspace f).X)
        (fun _ ↦ (1 : ℤ)) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
