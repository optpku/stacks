/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SubringOver

/-! Compatibility checks for subring-over categories. -/

@[expose] public section

open CategoryTheory
open Functor
open Functor.SubringOver

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

#check (CategoryTheory.Functor.SubringOver.mk :
  ∀ {x left : F} {p : F ⥤ ArtinianLocalAlgCat Λ k} (φ : left ⟶ x),
    Function.Injective (p.map φ).hom → SubringOver p x)

#check (CategoryTheory.Functor.SubringOver.IsMinimal :
  {p : F ⥤ ArtinianLocalAlgCat Λ k} → {x : F} → SubringOver p x → Prop)
