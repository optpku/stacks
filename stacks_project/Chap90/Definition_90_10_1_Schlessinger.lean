/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Schlessinger's conditions (S1) and (S2)

A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies (S1) when it is cofibered in
groupoids and every cospan with surjective second base leg completes over a pullback.
Condition (S2) is completion over `A ⟶ k ← k[ε]` and comparison by a fibre morphism.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

#check (CategoryTheory.Functor.HasSchlessingerS1 p : Prop)

#check (CategoryTheory.Functor.HasSchlessingerS2 p : Prop)
