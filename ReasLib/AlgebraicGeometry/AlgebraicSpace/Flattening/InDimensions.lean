/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.InDimensions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# The flat-in-dimensions functor on algebraic spaces

This module defines the subterminal functor on schemes over an algebraic space `Y`
that records the base changes on which a finite-type quasi-coherent module is
flat over the base in dimensions at least a fixed natural number.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/-- Flatness in dimensions at least `n` is preserved when the test scheme over `Y`
is changed further. -/
theorem flatInDimensionsGE_pullback {T T' : SchemeOver Y} (g : T' ⟶ T)
    (h : Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n) :
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T'.hom ℱ) (pullback.snd f T'.hom) n :=
  sorry

/-- The subfunctor of the terminal `PUnit` functor cut out by flatness of the
base-changed module in dimensions at least `n`. -/
def flatInDimensionsSubfunctor :
    CategoryTheory.Subfunctor
      ((Functor.const (SchemeOver Y)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ Modules.flatOverInDimensionsGE
    (Modules.baseChangeModule f T.unop.hom ℱ) (pullback.snd f T.unop.hom) n
  map g _ h := flatInDimensionsGE_pullback f ℱ n g.unop h

/-- Membership of the terminal section is exactly flatness of the base-changed
module in dimensions at least `n`. -/
theorem mem_flatInDimensionsSubfunctor (T : SchemeOver Y) :
    PUnit.unit ∈ (flatInDimensionsSubfunctor f ℱ n).obj (op T) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n :=
  Iff.rfl

/-- The contravariant subterminal functor recording flatness of the base-changed
module in dimensions at least `n`. -/
def flatInDimensionsFunctor : (SchemeOver Y)ᵒᵖ ⥤ Type u :=
  (flatInDimensionsSubfunctor f ℱ n).toFunctor

/-- An object value of the flat-in-dimensions functor is inhabited exactly when
the base-changed module is flat over the base in dimensions at least `n`. -/
theorem flatInDimensionsFunctor_nonempty_iff (T : SchemeOver Y) :
    Nonempty ((flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n :=
  by
    constructor
    · rintro ⟨x⟩
      exact x.property
    · intro h
      exact ⟨⟨PUnit.unit, h⟩⟩

/-- An object value of the flat-in-dimensions functor is empty exactly when the
base-changed module is not flat over the base in dimensions at least `n`. -/
theorem flatInDimensionsFunctor_isEmpty_iff (T : SchemeOver Y) :
    IsEmpty ((flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n :=
  by
    constructor
    · intro h hflat
      exact h.false ⟨PUnit.unit, hflat⟩
    · intro h
      exact ⟨fun x ↦ h x.property⟩

/-- Every object value of the flat-in-dimensions functor has at most one element. -/
instance flatInDimensionsFunctorObjSubsingleton (T : SchemeOver Y) :
    Subsingleton ((flatInDimensionsFunctor f ℱ n).obj (op T)) :=
  inferInstanceAs (Subsingleton (Subtype (fun _ : (PUnit : Type u) ↦
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n)))

/-- The functor value at the test scheme specified by `a : ofOver T ⟶ Y` is
inhabited exactly when the base change of `ℱ` along `a` is flat over `T` in
dimensions at least `n`. -/
theorem flatInDimensionsFunctor_nonempty_iff_mk {T : Over S} (a : ofOver T ⟶ Y) :
    Nonempty ((flatInDimensionsFunctor f ℱ n).obj (op (SchemeOver.mk a))) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n :=
  flatInDimensionsFunctor_nonempty_iff f ℱ n (SchemeOver.mk a)

/-- The functor value at the test scheme specified by `a : ofOver T ⟶ Y` is
empty exactly when the base change of `ℱ` along `a` is not flat over `T` in
dimensions at least `n`. -/
theorem flatInDimensionsFunctor_isEmpty_iff_mk {T : Over S} (a : ofOver T ⟶ Y) :
    IsEmpty ((flatInDimensionsFunctor f ℱ n).obj (op (SchemeOver.mk a))) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n :=
  flatInDimensionsFunctor_isEmpty_iff f ℱ n (SchemeOver.mk a)

end AlgebraicGeometry.AlgebraicSpace.Flattening
