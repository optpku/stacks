/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.6.1: a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable
if there exists `R : CompleteLocalAlgCat Λ k` with `F ≅ restrictedCoyoneda R`. -/
@[stacks 06GX]
#check (CategoryTheory.Functor.IsProrepresentable : (ArtinianLocalAlgCat Λ k ⥤ Type u) → Prop)
