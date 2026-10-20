module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SelfFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing

/-!
# Local-ring dimensions of smooth self 2-fibre products

For a smooth scheme morphism to a locally Noetherian algebraic stack, the
local-ring dimension of the self 2-fibre product is the sum of the source
local-ring dimension and the fibre local-ring dimension at the diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Let `X` be a locally Noetherian algebraic stack. Let
`p : GroupoidsOver.slice U ⟶ X` be a smooth morphism and let `u` be a point of
`U`. Then
`dimensionDiff (ringKrullDim (Scheme.etaleLocalRing U.left ubar))
  (AlgebraicSpace.fiberStalkDimAt s (Points.map e (ofOver.pointsEquiv U u)))`
equals
`dimensionDiff (d + d)
  (ringKrullDim (AlgebraicSpace.etaleLocalRing R ((ofScheme ubar).map e)))`,
where `d = ringKrullDim (Scheme.etaleLocalRing U.left ubar)`, the algebraic
space `R` represents the self 2-fibre product of `p` with projections `s`, `t`
and diagonal `e`, and the fibre of `s` over `u` is measured by
`fiberStalkDimAt`. -/
@[stacks 0DS8]
theorem smoothSelfFibre_etaleLocalRingDim_eq {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u) :
    dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) =
      dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
          ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (ringKrullDim
          (AlgebraicSpace.etaleLocalRing R
            ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e))) :=
  sorry

/-- The Krull dimension of the étale local ring of
`R` at `e(ubar)` equals `ringKrullDim` of the étale local ring of `U` at `ubar`
plus `fiberStalkDimAt s` at `e(u)`. -/
theorem smoothSelfFibre_etaleLocalRingDim_add {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u) :
    ringKrullDim
        (AlgebraicSpace.etaleLocalRing R
          ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e)) =
      ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
        AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e
            (AlgebraicSpace.ofOver.pointsEquiv U u)) :=
  sorry

/-- The identity in terms of `localRingDimAt` and `fiberStalkDimAt`, without a
chosen geometric point. -/
theorem smoothSelfFibre_localRingDimAt_eq {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) :
    dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) =
      dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u) +
          AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.localRingDimAt
          (AlgebraicSpace.Points.map e
            (AlgebraicSpace.ofOver.pointsEquiv U u))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
