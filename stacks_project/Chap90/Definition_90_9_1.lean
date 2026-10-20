/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory

/-!
# Smooth or unobstructed categories cofibered in groupoids

A category cofibered in groupoids over `C_Λ` is smooth, or unobstructed, when
its structure morphism is a smooth morphism of categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]

/- Definition 90.9.1 -/
@[stacks 06HP] #check (CategoryTheory.Functor.IsSmooth :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op], Prop)
