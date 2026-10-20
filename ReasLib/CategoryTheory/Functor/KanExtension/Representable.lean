/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left Kan extensions of representable presheaves

This module installs the canonical left Kan extension of a representable
presheaf along the opposite of a functor and exposes its representing
isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe v u₁ u₂

namespace CategoryTheory.Functor.LeftKanExtension.Representable

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]

/-- The representable presheaf at `u.obj U` is the canonical left Kan extension of the
representable presheaf at `U` along `u.op`. -/
noncomputable instance hasExtension (u : C ⥤ D) (U : C) :
    u.op.HasLeftKanExtension (yoneda.obj U) :=
  HasLeftKanExtension.mk (yoneda.obj (u.obj U)) (yonedaMap u U)

/-- The chosen left Kan extension of a representable presheaf is canonically represented by the
image of its representing object. -/
noncomputable def iso (u : C ⥤ D) (U : C) :
    u.op.leftKanExtension (yoneda.obj U) ≅ yoneda.obj (u.obj U) :=
  Functor.leftKanExtensionUnique
    (u.op.leftKanExtension (yoneda.obj U))
    (u.op.leftKanExtensionUnit (yoneda.obj U))
    (yoneda.obj (u.obj U))
    (yonedaMap u U)

end CategoryTheory.Functor.LeftKanExtension.Representable
