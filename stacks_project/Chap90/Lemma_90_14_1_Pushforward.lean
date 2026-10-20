/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SubringOver.Pushforward

/-! Compatibility checks for coimage pushforward on subring-over categories. -/

@[expose] public section

open CategoryTheory
open Functor
open Functor.SubringOver

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

#check (CategoryTheory.Functor.SubringOver.pushforward :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] {x y : F},
    (y ⟶ x) → SubringOver p y ⥤ SubringOver p x)

#check (CategoryTheory.Functor.SubringOver.pushforward_obj_image :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] {x y : F}
    (φ : y ⟶ x) (a : SubringOver p y),
    p.obj ((pushforward p φ).obj a).obj.left =
      ArtinianLocalAlgCat.image (p.map (arrow a ≫ φ)))
