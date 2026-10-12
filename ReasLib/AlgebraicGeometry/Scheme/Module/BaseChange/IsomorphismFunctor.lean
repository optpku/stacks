/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.Map

/-!
# The isomorphism functor of a module morphism

This module defines the subterminal functor that records the base changes on which a morphism
of quasicoherent scheme modules is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The subfunctor of the terminal `PUnit` functor cut out by invertibility of the
base-changed module morphism. -/
def isomorphismSubfunctor (u : ℱ ⟶ 𝒢) :
    CategoryTheory.Subfunctor
      ((Functor.const (Over S)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ IsIso (baseChangeMap f T.unop.hom u)
  map a _ h := baseChangeMap_isIso_of_over f u a.unop h

/-- Membership of the terminal section is exactly invertibility of the base-changed module
morphism. -/
theorem mem_isomorphismSubfunctor (u : ℱ ⟶ 𝒢) (T : Over S) :
    PUnit.unit ∈ (isomorphismSubfunctor f u).obj (op T) ↔
      IsIso (baseChangeMap f T.hom u) := sorry

/-- The contravariant subterminal functor recording where a module morphism becomes an
isomorphism after base change. -/
def isomorphismFunctor (u : ℱ ⟶ 𝒢) : (Over S)ᵒᵖ ⥤ Type u :=
  (isomorphismSubfunctor f u).toFunctor

/-- Every object value of the isomorphism functor has at most one element. -/
instance isomorphismFunctorObjSubsingleton (u : ℱ ⟶ 𝒢) (T : Over S) :
    Subsingleton ((isomorphismFunctor f u).obj (op T)) := sorry

/-- An object value of the isomorphism functor is inhabited exactly when the base-changed
morphism is an isomorphism. -/
theorem isomorphismFunctor_obj_nonempty_iff (u : ℱ ⟶ 𝒢) (T : Over S) :
    Nonempty ((isomorphismFunctor f u).obj (op T)) ↔
      IsIso (baseChangeMap f T.hom u) := sorry

/-- An object value of the isomorphism functor is empty exactly when the base-changed morphism
is not an isomorphism. -/
theorem isomorphismFunctor_obj_isEmpty_iff (u : ℱ ⟶ 𝒢) (T : Over S) :
    IsEmpty ((isomorphismFunctor f u).obj (op T)) ↔
      ¬ IsIso (baseChangeMap f T.hom u) := sorry

end AlgebraicGeometry.Scheme.Modules
