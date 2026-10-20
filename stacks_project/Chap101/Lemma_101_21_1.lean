module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Slicing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 101.21.1: A regular sequence on a cartesian field fibre of a flat,
locally finitely presented morphism to an algebraic stack cuts out a flat,
locally finitely presented morphism after shrinking around the projected point. -/
@[stacks 06MD] #check
  (AlgebraicGeometry.AlgebraicStack.exists_openSubspace_vanishing_flat_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U) {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F) (zbar : AlgebraicSpace.GeometricPoint F)
    (hz : zbar.liesOver z)
    (hreg : ∀ (V : AlgebraicSpace.smallEtaleSite U)
        (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V),
      RingTheory.Sequence.IsRegular (AlgebraicSpace.etaleLocalRing F zbar)
        (List.ofFn fun i ↦
          globalSectionsToRepresentedFiberEtaleLocalRingAt e zbar V l (fs i))),
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Flat (vanishingToStack f fs W) ∧
          LocallyOfFinitePresentation (vanishingToStack f fs W))
