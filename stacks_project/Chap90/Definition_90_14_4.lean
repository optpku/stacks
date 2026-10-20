/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    {F : Type (u + 1)} [Category.{u + 1} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p)

/- Definition 90.14.4: a versal formal object ξ of a predeformation category F
is minimal when every morphism of formal objects ξ' ⟶ ξ has
Function.Surjective underlying complete-local algebra map. A minimal versal
formal object is also called miniversal. This is owned by
FormalObject.IsMinimalVersal. -/
@[stacks 06T4] #check (FormalObject.IsMinimalVersal ξ : Prop)

variable [FormalObject.IsMinimalVersal ξ]

#check (FormalObject.IsMinimalVersal.spec ξ :
  ∀ {η : FormalObject p} (f : η ⟶ ξ), Function.Surjective f.base.hom)
