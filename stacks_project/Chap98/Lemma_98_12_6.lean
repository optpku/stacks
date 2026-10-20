module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.12.6. A representing Yoneda base change is smooth at every finite
type point lying over a point where the original object is versal. -/
@[stacks 0CXM] #check
  (AlgebraicGeometry.GroupoidsOver.smoothAt_baseChange_of_isVersalAt :
    ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [HasRimSchlessinger X]
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_lft : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {V : Scheme.{u}} (hV : V ⟶ S) [LocallyOfFiniteType hV] (y : X.total)
    (hy : X.p.obj y = Over.mk hV) (Z : AlgebraicSpace S)
    (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU))
    (hZ : representsYonedaFibreProduct hU x hx hV y hy Z toV toU)
    (z0 : AlgebraicSpace.Points Z) (hz0 : AlgebraicSpace.IsFiniteTypePoint z0)
    (h_over : AlgebraicSpace.Points.map toU z0 =
      AlgebraicSpace.ofOver.pointsEquiv (Over.mk hU) u0),
    AlgebraicSpace.SmoothAt toV z0)

end AlgebraicGeometry.GroupoidsOver
