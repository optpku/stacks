/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor

/-!
# The category of algebraic spaces over schemes

An object of `Spaces` over a scheme `S` is a morphism `X ⟶ ofOver U` of algebraic
spaces over `S`, with `U` a scheme over `S`. Morphisms are commutative squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category `Spaces` of algebraic spaces over schemes over `S`: objects are morphisms
`X ⟶ ofOver U` with `U : Over S`, and morphisms are commutative squares of algebraic
spaces over `S`. -/
abbrev Spaces (S : Scheme.{u}) :=
  Comma (𝟭 (AlgebraicSpace S)) (ofOverFunctor S)

namespace Spaces

/-- Package a morphism `X ⟶ ofOver U` as an object of `Spaces S`. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S} (pX : X ⟶ ofOver U) :
    Spaces S :=
  { left := X, right := U, hom := pX }

/-- The functor `p : Spaces S ⥤ Over S` sending `X ⟶ ofOver U` to `U`. -/
abbrev p {S : Scheme.{u}} : Spaces S ⥤ Over S :=
  Comma.snd (𝟭 (AlgebraicSpace S)) (ofOverFunctor S)

end Spaces

end AlgebraicGeometry.AlgebraicSpace
