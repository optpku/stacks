/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverPostScheme

/-!
The comparison with the big site agrees with postcomposition by the underlying
scheme-valued projection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (CategoryTheory.Functor.overPostScheme.eq_post_forget :
  ∀ {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) (x : 𝒳),
    Functor.overPostScheme p x = Over.post (p ⋙ Over.forget S))
