/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Pro

@[expose] public section

/-!
# Functoriality of Derived Stagewise Pro-Isomorphisms

This leaf records identity and composition formulas for canonical sequential
representatives. Closure and preservation of the stagewise pro-isomorphism
property are inherited from the neutral `MorphismProperty` API.
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Pro

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

namespace representative

/-- The representative of an identity derived morphism is the identity
sequential representative. -/
@[simp]
theorem id (K : DerivedCategory (SequentialInverseSystem A)) :
    representative (𝟙 K) =
      _root_.CategoryTheory.Pro.SequentialHom.id (Stage.tower K) := sorry

/-- Canonical sequential representatives preserve composition. -/
@[simp]
theorem comp {K L M : DerivedCategory (SequentialInverseSystem A)}
    (f : K ⟶ L) (g : L ⟶ M) :
    _root_.CategoryTheory.Pro.SequentialHom.comp
        (representative f) (representative g) =
      representative (f ≫ g) := sorry

end representative

end CategoryTheory.DerivedLimit.Pro
