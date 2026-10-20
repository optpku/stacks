module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Hull
import StacksCheckRecall

/-!
# Hulls in the classical and separable cases

A predeformation functor satisfying Schlessinger's conditions and having a
finite-dimensional tangent space admits a hull in the classical or separable case.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.15.6: in the classical case, the Schlessinger hypotheses give a hull. -/
@[stacks 06IY] #check (CategoryTheory.Functor.exists_isHull :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [CategoryTheory.Functor.IsPredeformationCategory
      (FormalObject.elementsProjectionULift F)]
    [CategoryTheory.Functor.HasSchlessingerS1
      (FormalObject.elementsProjectionULift F)]
    [CategoryTheory.Functor.HasSchlessingerS2
      (FormalObject.elementsProjectionULift F)]
    [FiniteDimensional k
      ((CategoryTheory.Functor.fiberIsoClassFunctor
        (FormalObject.elementsProjectionULift F)).obj
        (ArtinianLocalAlgCat.dualNumber Λ k))]
    [ArtinianLocalAlgCat.IsClassical Λ k],
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F),
      FormalObject.IsHull ξ)

#check (CategoryTheory.Functor.exists_isHull_of_isSeparable :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [CategoryTheory.Functor.IsPredeformationCategory
      (FormalObject.elementsProjectionULift F)]
    [CategoryTheory.Functor.HasSchlessingerS1
      (FormalObject.elementsProjectionULift F)]
    [CategoryTheory.Functor.HasSchlessingerS2
      (FormalObject.elementsProjectionULift F)]
    [FiniteDimensional k
      ((CategoryTheory.Functor.fiberIsoClassFunctor
        (FormalObject.elementsProjectionULift F)).obj
        (ArtinianLocalAlgCat.dualNumber Λ k))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F),
      FormalObject.IsHull ξ)
