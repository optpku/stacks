/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inclusion compatibility for bounded exact-derived transformations

Forgetting a restricted exact-derived natural transformation agrees with
restricting the ambient derived transformation along the source inclusion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus.map

/-- Forgetting a bounded-below exact-derived transformation recovers the
ambient derived transformation after the bounded-below inclusion. -/
@[simp, stacks 015F "bounded-below exact-derived transformation inclusion compatibility"]
theorem whiskerRight_ι {F G : A ⥤ₑ B} (α : F ⟶ G) :
    Functor.whiskerRight (Plus.map α) DerivedCategory.Plus.ι =
      Functor.whiskerLeft DerivedCategory.Plus.ι
        (ExactFunctor.MapDerivedCategory.map α) := sorry

end Plus.map

namespace Minus.map

/-- Forgetting a bounded-above exact-derived transformation recovers the
ambient derived transformation after the bounded-above inclusion. -/
@[simp, stacks 015F "bounded-above exact-derived transformation inclusion compatibility"]
theorem whiskerRight_ι {F G : A ⥤ₑ B} (α : F ⟶ G) :
    Functor.whiskerRight (Minus.map α) DerivedCategory.Minus.ι =
      Functor.whiskerLeft DerivedCategory.Minus.ι
        (ExactFunctor.MapDerivedCategory.map α) := sorry

end Minus.map

namespace Bounded.map

/-- Forgetting a bounded exact-derived transformation recovers the ambient
derived transformation after the bounded inclusion. -/
@[simp, stacks 015F "bounded exact-derived transformation inclusion compatibility"]
theorem whiskerRight_ι {F G : A ⥤ₑ B} (α : F ⟶ G) :
    Functor.whiskerRight (Bounded.map α) DerivedCategory.Bounded.ι =
      Functor.whiskerLeft DerivedCategory.Bounded.ι
        (ExactFunctor.MapDerivedCategory.map α) := sorry

end Bounded.map

end CategoryTheory.ExactFunctor.Derived
