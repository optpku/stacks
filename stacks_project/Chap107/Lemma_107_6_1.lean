module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SelfFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.6.1
For a smooth scheme morphism to a locally Noetherian algebraic stack, the
local-ring dimension difference equals twice the scheme local-ring dimension
minus the self 2-fibre product local-ring dimension at the diagonal.
-/
@[stacks 0DS8] #check
  (AlgebraicGeometry.AlgebraicStack.smoothSelfFibre_etaleLocalRingDim_eq :
    ∀ {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u),
    dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) =
      dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
          ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (ringKrullDim
          (AlgebraicSpace.etaleLocalRing R
            ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e))))

end AlgebraicGeometry.AlgebraicStack
