/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange

/-!
# The flattening functor of a quasicoherent module

This module defines the subterminal functor recording the scheme base changes over which a
quasicoherent module becomes flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The condition that the pullback of `ℱ` to `X ×_S T` is flat over `T`. -/
def isFlat (T : Over S) : Prop :=
  Scheme.Modules.flatOver (Scheme.Modules.baseChangeModule f T.hom ℱ)
    (CategoryTheory.Limits.pullback.snd f T.hom)

/-- Relative flatness after scheme base change is expressed by `flatOver` along the second
projection. -/
theorem isFlat_iff (T : Over S) :
    isFlat f ℱ T ↔
      Scheme.Modules.flatOver (Scheme.Modules.baseChangeModule f T.hom ℱ)
        (CategoryTheory.Limits.pullback.snd f T.hom) := sorry

/-- Flatness after base change is preserved by restriction along a morphism of `S`-schemes. -/
theorem isFlat_of_hom {T U : Over S} (g : T ⟶ U) (h : isFlat f ℱ U) :
    isFlat f ℱ T := sorry

/-- The subfunctor of the terminal `PUnit` presheaf cut out by flatness after base change. -/
def subfunctor :
    CategoryTheory.Subfunctor ((Functor.const (Over S)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := { _x | isFlat f ℱ T.unop }
  map g _ h := isFlat_of_hom f ℱ g.unop h

/-- Membership in the flattening subfunctor is exactly flatness after base change. -/
theorem mem_subfunctor_obj (T : Over S) (x : PUnit.{u + 1}) :
    x ∈ (subfunctor f ℱ).obj (op T) ↔ isFlat f ℱ T := sorry

/-- The subterminal contravariant functor recording flatness after scheme base change. -/
def functor : (Over S)ᵒᵖ ⥤ Type u :=
  (subfunctor f ℱ).toFunctor

/-- The fiber of the flattening functor is inhabited exactly when the base-changed module is
flat over the new base. -/
theorem functor_obj_nonempty_iff (T : Over S) :
    Nonempty ((functor f ℱ).obj (op T)) ↔ isFlat f ℱ T := sorry

/-- Every two elements of a fiber of the flattening functor are equal. -/
theorem functor_obj_unique (T : Over S) (x y : (functor f ℱ).obj (op T)) :
    x = y := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
