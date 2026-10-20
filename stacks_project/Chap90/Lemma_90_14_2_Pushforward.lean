/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.SmallestDescent

/-! Compatibility check for smallest-descent morphisms of formal objects. -/

@[expose] public section

open CategoryTheory
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

#check (FormalObject.Hom.IsSmallestDescent :
  ∀ [IsFibered.InGroupoids p.op] {ξ' ξ : FormalObject p}, (ξ' ⟶ ξ) → Prop)
