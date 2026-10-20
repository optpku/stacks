module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Slicing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

/- Lemma 76.28.1: A regular sequence on a field-valued fibre cuts out a flat,
locally finitely presented subspace after shrinking around the image of the point. -/
@[stacks 06LW] #check (AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_vanishingSubspace_flat_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint Y) {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (z : Points (fieldFiber f p))
    (zbar : GeometricPoint (fieldFiber f p)) (hz : zbar.liesOver z)
    (hreg : ∀ (U : smallEtaleSite X)
        (l : (toSmallEtalePoint (zbar.map (fieldFiberι f p))).fiber.obj U),
      RingTheory.Sequence.IsRegular (etaleLocalRing (fieldFiber f p) zbar)
        (List.ofFn fun i ↦
          globalSectionsToFiberEtaleLocalRingAt f p zbar U l (fs i))),
    ∃ U : OpenSubspace X,
      Points.map (fieldFiberι f p) z ∈ U.pointsSet ∧
        Flat (vanishingPullbackHom f fs U) ∧
          LocallyOfFinitePresentation (vanishingPullbackHom f fs U))
