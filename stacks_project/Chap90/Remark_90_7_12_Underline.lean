/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.Inverse

/-!
# Explicit restricted Yoneda inverse

The nilpotency-pushforward construction and its recovery isomorphism are available
through their mathematical owner.
-/

@[expose] public section

open CategoryTheory FormalObject CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
  (R : CompleteLocalAlgCat Λ k)

#check (FormalObject.toRestrictedHom (p := p) R :
  Functor.Fiber (Functor.completion p) R ⥤ RestrictedHom p R)

#check (FormalObject.toRestrictedHom_obj (p := p) R :
  ∀ (ξ : Functor.Fiber (Functor.completion p) R) (x : (restrictedCoyoneda R).Elements),
    ((toRestrictedHom R).obj ξ).obj x = toRestrictedHomObj ξ x ∧
      p.obj (((toRestrictedHom R).obj ξ).obj x) = x.1)

#check (FormalObject.fromRestrictedHom_toRestrictedHom (p := p) R :
  ∀ ξ : Functor.Fiber (Functor.completion p) R,
    (fromRestrictedHom p R).obj ((toRestrictedHom R).obj ξ) ≅ ξ)
