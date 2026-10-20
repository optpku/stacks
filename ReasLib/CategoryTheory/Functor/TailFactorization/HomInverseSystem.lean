/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.HomInverseSystem
public import ReasLib.CategoryTheory.Functor.TailFactorization

/-!
# Tail factorization and Hom inverse systems

Tail factorization is exactly the categorical factorization input needed to stabilize the images
in every contravariant representable functor.
-/

@[expose] public section

open CategoryTheory

universe uI vI uC vC

namespace CategoryTheory.Functor.HasTailFactorization

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-- Tail factorization makes the Hom inverse system into every target Mittag-Leffler. -/
@[stacks 059E "Hom inverse system"]
theorem homInverseSystem {F : I ⥤ C} (hF : F.HasTailFactorization) (N : C) :
    (F.homInverseSystem N).IsMittagLeffler := by
  intro i
  obtain ⟨j, f, hf⟩ := hF i.unop
  refine ⟨Opposite.op j, f.op, ?_⟩
  intro k g
  rintro _ ⟨q, rfl⟩
  obtain ⟨h, hh⟩ := hf k.unop g.unop
  refine ⟨h ≫ q, ?_⟩
  change (F.map g.unop).op.unop ≫ (h ≫ q) = (F.map f).op.unop ≫ q
  rw [Quiver.Hom.unop_op, Quiver.Hom.unop_op, ← Category.assoc, ← hh]

/-- Tail factorization makes every associated Hom inverse system Mittag-Leffler. -/
@[stacks 059E "all-target Hom criterion"]
theorem homMittagLeffler {F : I ⥤ C} (hF : F.HasTailFactorization) :
    F.HomMittagLeffler := fun N ↦ hF.homInverseSystem N

end CategoryTheory.Functor.HasTailFactorization
