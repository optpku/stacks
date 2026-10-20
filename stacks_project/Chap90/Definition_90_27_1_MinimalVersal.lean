/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable {F : Type (u + 1)} [Category.{u + 1} F]
  (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]

/- Definition 90.27.1: canonical identity towers and minimal versal formal objects. -/
#check (CompleteLocalAlgCat.identityFormalObject :
  ∀ R : CompleteLocalAlgCat Λ k, FormalObject (CompleteLocalAlgCat.identityProjection R))
#check (FormalObject.restrictedIdentity :
  ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ), (CompleteLocalAlgCat.restrictedCoyoneda R).Elements)
#check (FormalObject.restrictedIdentityMap :
  ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ),
    FormalObject.restrictedIdentity R (n + 1) ⟶ FormalObject.restrictedIdentity R n)
variable (ξ : FormalObject p)
#check (FormalObject.IsVersal ξ : Prop)
#check (FormalObject.IsMinimalVersal ξ : Prop)
#check (FormalObject.IsMinimalPresentation p :
  ∀ U : ArtinianLocalAlgCat Λ k ⥤ Type u,
    (BasedCategory.ofFunctor (FormalObject.elementsProjectionULift U) ⥤ᵇ
      BasedCategory.ofFunctor p) → Prop)
