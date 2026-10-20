/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The isomorphism functor of a module morphism on an algebraic space

This module defines the subterminal functor on schemes over an algebraic space `B` that records
the base changes on which a morphism of quasi-coherent modules is an isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- Invertibility of a base-changed module morphism is preserved by restriction of the test
scheme over `B`. -/
theorem baseChangeMap_isIso {T T' : SchemeOver B} (φ : T' ⟶ T) (u : ℱ ⟶ 𝒢)
    (h : IsIso (baseChangeMap f T.hom u)) :
    IsIso (baseChangeMap f T'.hom u) :=
  sorry

/-- The subfunctor of the terminal `PUnit` functor cut out by invertibility of the
base-changed module morphism. -/
def isomorphismSubfunctor (u : ℱ ⟶ 𝒢) :
    CategoryTheory.Subfunctor
      ((Functor.const (SchemeOver B)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ IsIso (baseChangeMap f T.unop.hom u)
  map a _ h := baseChangeMap_isIso f a.unop u h

/-- Membership of the terminal section is exactly invertibility of the base-changed module
morphism. -/
theorem mem_isomorphismSubfunctor (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    PUnit.unit ∈ (isomorphismSubfunctor f u).obj (op T) ↔
      IsIso (baseChangeMap f T.hom u) :=
  sorry

/-- The contravariant subterminal functor recording where a module morphism becomes an
isomorphism after base change to a scheme over `B`. -/
def isomorphismFunctor (u : ℱ ⟶ 𝒢) : (SchemeOver B)ᵒᵖ ⥤ Type u :=
  (isomorphismSubfunctor f u).toFunctor

/-- Every object value of the isomorphism functor has at most one element. -/
instance isomorphismFunctorObjSubsingleton (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    Subsingleton ((isomorphismFunctor f u).obj (op T)) :=
  sorry

/-- An object value of the isomorphism functor is inhabited exactly when the base-changed
morphism is an isomorphism. -/
theorem isomorphismFunctor_obj_nonempty_iff (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor f u).obj (op T)) ↔
      IsIso (baseChangeMap f T.hom u) :=
  sorry

/-- An object value of the isomorphism functor is empty exactly when the base-changed morphism
is not an isomorphism. -/
theorem isomorphismFunctor_obj_isEmpty_iff (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    IsEmpty ((isomorphismFunctor f u).obj (op T)) ↔
      ¬ IsIso (baseChangeMap f T.hom u) :=
  sorry

/-- At the test scheme specified by `a`, the isomorphism functor is inhabited exactly when
the pullback of `u` along `X ×_B T ⟶ X` is an isomorphism. -/
theorem isomorphismFunctor_obj_nonempty_iff_mk {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢) :
    Nonempty ((isomorphismFunctor f u).obj (op (SchemeOver.mk a))) ↔
      IsIso (baseChangeMap f a u) :=
  sorry

/-- At the test scheme specified by `a`, the isomorphism functor is empty exactly when
the pullback of `u` along `X ×_B T ⟶ X` is not an isomorphism. -/
theorem isomorphismFunctor_obj_isEmpty_iff_mk {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢) :
    IsEmpty ((isomorphismFunctor f u).obj (op (SchemeOver.mk a))) ↔
      ¬ IsIso (baseChangeMap f a u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
