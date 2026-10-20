/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Pointwise
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic

/-!
# Freeness at generic points of fibres

This module defines the subterminal functor recording the base changes on which a finite-type
quasicoherent module is free of a fixed rank near the generic point of every fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/-- The base change of `ℱ` is free of rank `p` near the generic point of the fibre over every
point of `T`. -/
def IsFreeAtGenericPoints (T : Over S) : Prop :=
  ∀ t : T.left,
    SheafOfModules.IsFreeOfRankAt p (Scheme.Modules.baseChangeModule f T.hom ℱ)
      ((pullback.snd f T.hom).fiberι t (genericPoint ((pullback.snd f T.hom).fiber t)))

/-- The pointwise open-neighbourhood characterization of freeness at the generic points of the
fibres. -/
theorem IsFreeAtGenericPoints.iff (T : Over S) :
    IsFreeAtGenericPoints f ℱ p T ↔
      ∀ t : T.left,
        ∃ (U : (pullback f T.hom : Scheme.{u}).Opens)
          (_ : (pullback.snd f T.hom).fiberι t
            (genericPoint ((pullback.snd f T.hom).fiber t)) ∈ U),
          Nonempty
            ((Scheme.Modules.baseChangeModule f T.hom ℱ).over U ≅
              SheafOfModules.freeFin p) := sorry

/-- Freeness near all fibre generic points is preserved by a further base change. -/
theorem IsFreeAtGenericPoints.pullback {T T' : Over S} (g : T' ⟶ T)
    (h : IsFreeAtGenericPoints f ℱ p T) :
    IsFreeAtGenericPoints f ℱ p T' := sorry

/-- The subfunctor of the terminal `PUnit` functor cut out by freeness of rank `p` near all fibre
generic points. -/
def freeAtGenericPointsSubfunctor :
    CategoryTheory.Subfunctor
      ((Functor.const (Over S)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ IsFreeAtGenericPoints f ℱ p T.unop
  map g _ h := IsFreeAtGenericPoints.pullback f ℱ p g.unop h

/-- Membership of the terminal section in the generic-point freeness subfunctor is exactly the
defining freeness condition. -/
theorem mem_freeAtGenericPointsSubfunctor (T : Over S) :
    PUnit.unit ∈ (freeAtGenericPointsSubfunctor f ℱ p).obj (op T) ↔
      IsFreeAtGenericPoints f ℱ p T := sorry

/-- The subterminal functor whose value records freeness of rank `p` near every fibre generic
point. -/
def freeAtGenericPointsFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (freeAtGenericPointsSubfunctor f ℱ p).toFunctor

/-- The generic-point freeness functor is inhabited exactly when the base-changed module is free
of rank `p` near the generic point of every fibre. -/
theorem freeAtGenericPointsFunctor_nonempty_iff (T : Over S) :
    Nonempty ((freeAtGenericPointsFunctor f ℱ p).obj (op T)) ↔
      IsFreeAtGenericPoints f ℱ p T := sorry

end AlgebraicGeometry.Scheme.Flattening
