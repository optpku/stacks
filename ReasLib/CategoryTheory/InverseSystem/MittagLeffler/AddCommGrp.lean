/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.CofilteredSystem
public import ReasLib.CategoryTheory.InverseSystem.Coproduct
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler

/-!
# Mittag-Leffler Towers of Abelian Groups

This leaf compares the categorical image-stabilization condition for sequential inverse systems
with mathlib's eventual-range condition on the underlying type-valued diagram.
@stack 0CQA
-/

@[expose] public section

open CategoryTheory.Limits

universe v

namespace CategoryTheory.SequentialInverseSystem

namespace IsMittagLeffler

/-- The image-stabilization condition on a sequential inverse system of abelian groups is
equivalent to mathlib's eventual-range Mittag-Leffler condition on its underlying type-valued
diagram. -/
theorem iff_forget (F : SequentialInverseSystem AddCommGrpCat.{v}) :
    SequentialInverseSystem.IsMittagLeffler F ↔
      Functor.IsMittagLeffler (F ⋙ forget AddCommGrpCat.{v}) := sorry

end IsMittagLeffler

end CategoryTheory.SequentialInverseSystem

namespace CategoryTheory.SequentialInverseSystem.IsMittagLeffler

/-- Lemma 15.87.14 (Emmanouil) [0CQA]: a sequential inverse system of abelian groups is
Mittag-Leffler exactly when both its canonical Milnor cokernel and that of its stagewise
countable coproduct vanish. These are the neutral `Milnor.ProductCone.canonicalR1` models of
the first derived inverse limits. -/
@[stacks 0CQA]
theorem iff_r1Vanishing_of_countableCoproduct
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    A.IsMittagLeffler ↔
      IsZero (Milnor.ProductCone.canonicalR1 A) ∧
        IsZero (Milnor.ProductCone.canonicalR1 A.countableCoproduct) := sorry

end CategoryTheory.SequentialInverseSystem.IsMittagLeffler
