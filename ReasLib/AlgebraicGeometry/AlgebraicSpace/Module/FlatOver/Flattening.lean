module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# The flattening functor of a quasi-coherent module on an algebraic space

This module defines the subterminal functor on schemes over an algebraic space `Y` that
records the base changes on which a quasi-coherent module becomes flat over the test scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The pullback `ℱ_T` of `ℱ` to `X ×_Y T`. -/
abbrev baseChange (T : SchemeOver Y) : (baseChangeSpace f T.hom).Modules :=
  baseChangeModule f T.hom ℱ

/-- `baseChange f ℱ T` is module pullback of `ℱ` along `X ×_Y T ⟶ X`. -/
theorem baseChange_eq (T : SchemeOver Y) :
    baseChange f ℱ T = baseChangeModule f T.hom ℱ :=
  sorry

/-- The condition that the pullback of `ℱ` to `X ×_Y T` is flat over `T`. -/
def isFlat (T : SchemeOver Y) : Prop :=
  flatOver (baseChange f ℱ T) (Limits.pullback.snd f T.hom)

/-- Relative flatness after base change is `flatOver` along the second projection. -/
theorem isFlat_iff (T : SchemeOver Y) :
    isFlat f ℱ T ↔
      flatOver (baseChangeModule f T.hom ℱ) (Limits.pullback.snd f T.hom) :=
  sorry

/-- Flatness after base change is preserved by restriction along a morphism of schemes over `Y`. -/
theorem isFlat_of_hom {T U : SchemeOver Y} (g : T ⟶ U) (h : isFlat f ℱ U) :
    isFlat f ℱ T :=
  sorry

/-- The subfunctor of the terminal `PUnit` presheaf cut out by flatness after base change. -/
def subfunctor :
    CategoryTheory.Subfunctor ((Functor.const (SchemeOver Y)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := { _x | isFlat f ℱ T.unop }
  map g _ h := isFlat_of_hom f ℱ g.unop h

/-- Membership of the terminal section is exactly flatness after base change. -/
theorem mem_subfunctor (T : SchemeOver Y) :
    PUnit.unit ∈ (subfunctor f ℱ).obj (op T) ↔ isFlat f ℱ T :=
  sorry

/-- The contravariant subterminal functor recording where `ℱ` becomes flat over a scheme over `Y`. -/
def functor : (SchemeOver Y)ᵒᵖ ⥤ Type u :=
  (subfunctor f ℱ).toFunctor

/-- Every object value of the flattening functor has at most one element. -/
instance functorObjSubsingleton (T : SchemeOver Y) :
    Subsingleton ((functor f ℱ).obj (op T)) :=
  sorry

/-- An object value of the flattening functor is inhabited exactly when the base-changed
module is flat over the test scheme. -/
theorem functor_obj_nonempty_iff (T : SchemeOver Y) :
    Nonempty ((functor f ℱ).obj (op T)) ↔ isFlat f ℱ T :=
  sorry

/-- An object value of the flattening functor is empty exactly when the base-changed module
is not flat over the test scheme. -/
theorem functor_obj_isEmpty_iff (T : SchemeOver Y) :
    IsEmpty ((functor f ℱ).obj (op T)) ↔ ¬ isFlat f ℱ T :=
  sorry

/-- The value at the test scheme with structural morphism `a` is inhabited exactly when
the base-changed module is flat over `T`. -/
theorem functor_obj_nonempty_iff_mk {T : Over S} (a : ofOver T ⟶ Y) :
    Nonempty ((functor f ℱ).obj (op (SchemeOver.mk a))) ↔
      flatOver (baseChangeModule f a ℱ) (Limits.pullback.snd f a) :=
  sorry

/-- The value at the test scheme with structural morphism `a` is empty exactly when
the base-changed module is not flat over `T`. -/
theorem functor_obj_isEmpty_iff_mk {T : Over S} (a : ofOver T ⟶ Y) :
    IsEmpty ((functor f ℱ).obj (op (SchemeOver.mk a))) ↔
      ¬ flatOver (baseChangeModule f a ℱ) (Limits.pullback.snd f a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Flattening
