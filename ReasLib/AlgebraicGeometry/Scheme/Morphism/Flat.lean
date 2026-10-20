/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism

/-!
# Pointwise flatness of scheme morphisms

This file specializes pointwise flatness of ringed-space morphisms to scheme morphisms and
relates it to mathlib's canonical scheme-morphism flatness class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- A scheme morphism is flat at `x` when its induced local-ring map at `x` is flat. -/
@[stacks 01U3]
abbrev flatAt (f : X ⟶ S) (x : X) : Prop :=
  RingedSpace.Hom.FlatAt f.toLRSHom.toShHom x

/-- Mathlib's canonical `Flat f` condition is equivalent to flatness at every source point. -/
@[stacks 01U3]
theorem flat_iff_forall_flatAt (f : X ⟶ S) :
    Flat f ↔ ∀ x : X, flatAt f x := sorry

end Scheme.Hom

/-- The morphism property of being both flat and surjective. -/
abbrev faithfullyFlatMorphismProperty :
    CategoryTheory.MorphismProperty Scheme.{u} :=
  ((@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.Surjective) :
    CategoryTheory.MorphismProperty Scheme.{u})

end AlgebraicGeometry
