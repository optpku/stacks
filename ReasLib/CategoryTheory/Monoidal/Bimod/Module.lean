/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module.Basic
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left and right modules over monoid objects

One-sided modules are bimodule objects whose other acting monoid is the tensor unit.  This file
packages that standard specialization together with its balanced tensor functor and the
categorical flatness predicate it induces.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Tensor

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A : Mon C}

/-- Balanced tensor with a fixed right `A`-module, as a functor on left `A`-modules. -/
@[stacks 0FSA "generic relative tensor functor"]
noncomputable def tensorFunctor (M : RightModule A) : LeftModule A ⥤ C :=
  tensorLeftUnderlying M

/-- The balanced tensor product of a right and a left module over a monoid object. -/
@[stacks 0FSA "generic relative tensor product"]
noncomputable abbrev tensor (M : RightModule A) (N : LeftModule A) : C :=
  (tensorFunctor M).obj N

/-- A right module is flat when its balanced tensor functor on left modules is exact. -/
@[stacks 0FSA "generic relative flatness"]
def IsFlat (M : RightModule A) : Prop :=
  exactFunctor (LeftModule A) C (tensorFunctor M)

/-- Flat right modules over `A` as an object property. -/
abbrev flatObjects (A : Mon C) : ObjectProperty (RightModule A) :=
  fun M ↦ IsFlat M

/-- Relative flatness is exactly exactness of the balanced tensor functor. -/
theorem isFlat_iff (M : RightModule A) :
    IsFlat M ↔ exactFunctor (LeftModule A) C (tensorFunctor M) := sorry

/-- The generic relative tensor is Mathlib's coequalizer-based bimodule tensor. -/
@[simp]
theorem tensor_eq (M : RightModule A) (N : LeftModule A) :
    tensor M N = (M.tensorBimod N).X := sorry

namespace LeftModule

/-- Balanced tensor with a fixed left `A`-module, as a functor on right `A`-modules. -/
@[stacks 0FSA "generic left relative tensor functor"]
noncomputable def tensorFunctor (N : LeftModule A) : RightModule A ⥤ C :=
  tensorRightUnderlying N

/-- The balanced tensor product determined by a fixed left module and a varying right module. -/
@[stacks 0FSA "generic left relative tensor product"]
noncomputable abbrev tensor (N : LeftModule A) (M : RightModule A) : C :=
  (tensorFunctor N).obj M

/-- A left module is flat when balanced tensoring with it is exact on right modules. -/
@[stacks 0FSA "generic left relative flatness"]
def IsFlat (N : LeftModule A) : Prop :=
  exactFunctor (RightModule A) C (tensorFunctor N)

/-- Flat left modules over `A` as an object property. -/
@[stacks 0FSA "generic flat left module object property"]
abbrev flatObjects (A : Mon C) : ObjectProperty (LeftModule A) :=
  fun N ↦ IsFlat N

/-- Left relative flatness is exactly exactness of the balanced tensor functor on right modules. -/
@[stacks 0FSA "generic left relative flatness criterion"]
theorem isFlat_iff (N : LeftModule A) :
    IsFlat N ↔ exactFunctor (RightModule A) C (tensorFunctor N) := sorry

/-- The left-oriented relative tensor is Mathlib's coequalizer-based bimodule tensor. -/
@[stacks 0FSA "generic left relative tensor comparison", simp]
theorem tensor_eq (N : LeftModule A) (M : RightModule A) :
    tensor N M = (M.tensorBimod N).X := sorry

end LeftModule

end Tensor

end CategoryTheory.Bimod

end
