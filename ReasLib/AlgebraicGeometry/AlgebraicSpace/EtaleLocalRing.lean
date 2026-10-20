module

public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic

/-!
# Étale local rings of algebraic spaces

The étale local ring at a geometric point is the stalk of the small étale structure sheaf.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stalk of the small étale structure sheaf as a commutative ring, with its
original stalk carrier and ring operations. -/
noncomputable def etaleLocalRing.asCommRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : CommRingCat.{u} where
  carrier :=
    ((GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
      (structureSheaf X).obj
  commRing := { (inferInstance : Ring _) with mul_comm := sorry }

/-- The étale local ring of an algebraic space at a geometric point is the stalk of the
structure sheaf on the small étale site at that geometric point. The geometric point lies
over `xbar.image ∈ |X|`. -/
noncomputable abbrev etaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : Type u :=
  etaleLocalRing.asCommRing X xbar

/-- The étale-site stalk is commutative, using the underlying ring operations of the
`RingCat` fiber. -/
@[reducible]
noncomputable def etaleLocalRingCommRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : CommRing (etaleLocalRing X xbar) :=
  (etaleLocalRing.asCommRing X xbar).commRing

end AlgebraicGeometry.AlgebraicSpace
