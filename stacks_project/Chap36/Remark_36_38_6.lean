module

import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Ring
import ReasLib.AlgebraicGeometry.Scheme.K0.Module
import StacksCheckRecall

open CategoryTheory

universe u

/- Remark 36.38.6 (1): the Grothendieck group of perfect complexes on a scheme is
canonically a commutative ring under derived tensor product. -/
@[stacks 0FDK] #check
  (AlgebraicGeometry.Scheme.K0.instCommRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      CommRing (AlgebraicGeometry.Scheme.K0 X))

#check
  (AlgebraicGeometry.Scheme.K0.mul_of :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (K L : AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect
        (X := X.toRingedSpace)),
      AlgebraicGeometry.Scheme.K0.mul X (TriangulatedK0.of K) (TriangulatedK0.of L) =
        TriangulatedK0.of (AlgebraicGeometry.Scheme.K0.tensorObj X K L))

#check
  (AlgebraicGeometry.Scheme.K0.one_eq :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (1 : AlgebraicGeometry.Scheme.K0 X) =
        TriangulatedK0.of (AlgebraicGeometry.Scheme.K0.unitObject X))

/- Remark 36.38.6 (2): the Grothendieck group of finite locally free modules on a scheme is
canonically a commutative ring under tensor product. -/
@[stacks 0FDK] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.instCommRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      CommRing (AlgebraicGeometry.Scheme.VectorBundleK0 X))

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.mul_of :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)),
      AlgebraicGeometry.Scheme.VectorBundleK0.mul X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E)
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) F) =
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (AlgebraicGeometry.Scheme.VectorBundleK0.tensorObj X E F))

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.one_eq :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (1 : AlgebraicGeometry.Scheme.VectorBundleK0 X) =
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (AlgebraicGeometry.Scheme.VectorBundleK0.unitObject X))

/- Remark 36.38.6 (3): the comparison from vector-bundle K₀ to perfect-complex K₀ is a
ring homomorphism. -/
@[stacks 0FDK] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
        AlgebraicGeometry.Scheme.K0 X)

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom_toAddMonoidHom :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom X).toAddMonoidHom =
        AlgebraicGeometry.Scheme.VectorBundleK0.toK0 X)

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom_of :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)),
      AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
        TriangulatedK0.of
          ((AlgebraicGeometry.Scheme.VectorBundleK0.toPerfect X).obj E))

/- Remark 36.38.6 (4): for a Noetherian scheme X, coherent K0' X is canonically a module
over the ring K0 X, with action induced by derived tensor product. -/
@[stacks 0FDK] #check
  (AlgebraicGeometry.Scheme.K0'.instModule :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X],
      Module (AlgebraicGeometry.Scheme.K0 X) (AlgebraicGeometry.Scheme.K0' X))

#check
  (AlgebraicGeometry.Scheme.K0'.smul_derivedK0Equiv_symm_of :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]
      (K : AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect
        (X := X.toRingedSpace))
      (M : DerivedCategory.Bounded.CohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)),
      AlgebraicGeometry.Scheme.K0'.smul X (TriangulatedK0.of K)
          ((AlgebraicGeometry.Scheme.K0'.derivedK0Equiv X).symm
            (TriangulatedK0.of M)) =
        (AlgebraicGeometry.Scheme.K0'.derivedK0Equiv X).symm
          (TriangulatedK0.of
            (AlgebraicGeometry.Scheme.K0'.tensorObj X K M)))
