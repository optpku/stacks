/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive right internal Hom functors

The target-variable functor of a chosen right internal Hom is additive because it is right
adjoint to additive tensoring by its fixed source object.
-/

@[expose] public section

universe u v

namespace CategoryTheory.RightInternalHom

open Opposite

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C]

/-- The target-variable functor of a chosen right internal Hom is additive. -/
@[stacks 0GWJ "additive right internal-Hom functor"]
instance homObjAdditive [MonoidalPreadditive C] (H : RightInternalHom C) (X : C) :
    (H.hom.obj (op X)).Additive :=
  (H.adj₂.adj X).right_adjoint_additive

variable [MonoidalPreadditive C] (H : RightInternalHom C) (X : C)

#synth (H.hom.obj (op X)).Additive

end CategoryTheory.RightInternalHom
