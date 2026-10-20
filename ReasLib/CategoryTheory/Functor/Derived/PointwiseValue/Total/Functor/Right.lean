/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Functor.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Right-Derived Functors as Functors of Pointwise Values

This file packages the objectwise total-to-pointwise right-derived comparisons as a natural
isomorphism and exposes its component computations.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The total right-derived functor, pulled back to the source, is naturally isomorphic to the
functor of its pointwise right-derived values. -/
@[stacks 05SA]
noncomputable def RightDerived.Value.totalNatIso
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseRightDerivedFunctor S] :
    S.Q ⋙ F.totalRightDerived S.Q S ≅ RightDerived.Value.functor F S :=
  RightDerived.Value.modelNatIso F S (F.totalRightDerived S.Q S)
    (F.totalRightDerivedUnit S.Q S)

namespace RightDerived.Value.totalNatIso

/-- The forward component of `RightDerived.Value.totalNatIso` is the canonical objectwise
total-to-pointwise comparison. -/
@[simp, stacks 05SA "total right-derived value natural isomorphism computation"]
theorem hom_app (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    (RightDerived.Value.totalNatIso F S).hom.app X =
      (RightDerived.Value.totalIso F S X).hom := sorry

/-- The inverse component of `RightDerived.Value.totalNatIso` is the inverse objectwise
pointwise comparison. -/
@[simp, stacks 05SA "total right-derived value natural isomorphism computation"]
theorem inv_app (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    (RightDerived.Value.totalNatIso F S).inv.app X =
      (RightDerived.Value.totalIso F S X).inv := sorry

end RightDerived.Value.totalNatIso

end CategoryTheory.Functor
