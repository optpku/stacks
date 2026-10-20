/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom

/-!
# Yoneda evaluation of restricted coyoneda morphisms

A based morphism from the category of elements of `restrictedCoyoneda R` to a
category cofibered in groupoids over `C_Λ` is evaluated on the identity
truncations of `R` to produce a formal object in the completion fibre over `R`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat

#check (FormalObject.RestrictedHom : (F ⥤ ArtinianLocalAlgCat Λ k) →
  CompleteLocalAlgCat Λ k → Type (max (u + 1) v))

#check (FormalObject.restrictedIdentity : ∀ (R : CompleteLocalAlgCat Λ k),
  ℕ → (restrictedCoyoneda R).Elements)

#check (FormalObject.restrictedIdentityMap : ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ),
  restrictedIdentity R (n + 1) ⟶ restrictedIdentity R n)

#check (FormalObject.fromRestrictedHom : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k),
  RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R)

#check (FormalObject.fromRestrictedHom_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (R : CompleteLocalAlgCat Λ k), (fromRestrictedHom p R).IsEquivalence)

end FormalObject
