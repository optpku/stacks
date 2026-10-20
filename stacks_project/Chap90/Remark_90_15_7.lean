module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.IsoClass

@[expose] public section

open CategoryTheory FormalObject
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Remark 90.15.7. The canonical image of a versal formal object is versal;
a bijective differential makes it a hull. -/
@[stacks 06IZ] #check (FormalObject.instIsVersal_isoClass :
    ∀ [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ],
    IsVersal (isoClass ξ))

#check (FormalObject.bijectiveDifferential_isoClass :
    ∀ [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) (h : BijectiveDifferential ξ),
    BijectiveDifferential (isoClass ξ))

#check (FormalObject.instIsHull_isoClass :
    ∀ [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsHull ξ],
    IsHull (isoClass ξ))

#check (FormalObject.isHull_isoClass :
    ∀ [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] (h : BijectiveDifferential ξ),
    IsHull (isoClass ξ))

#check (FormalObject.exists_isHull_isoClass :
    ∀ [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p]
    [FiniteDimensional k
      ((Functor.fiberIsoClassFunctor p).obj (ArtinianLocalAlgCat.dualNumber Λ k))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    ∃ ξ : FormalObject (Functor.isoClassProjection p), IsHull ξ)

#check (FormalObject.exists_isMinimalVersal_bijectiveDifferential :
    ∀ [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS1 p]
      [Functor.HasSchlessingerS2 p]
      [FiniteDimensional k
        ((Functor.fiberIsoClassFunctor p).obj (ArtinianLocalAlgCat.dualNumber Λ k))]
      [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
      ∃ ξ : FormalObject p,
        FormalObject.IsMinimalVersal ξ ∧ FormalObject.BijectiveDifferential ξ)
