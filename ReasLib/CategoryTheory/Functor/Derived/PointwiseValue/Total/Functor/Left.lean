/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Functor.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Left-Derived Functors as Functors of Pointwise Values

This file packages the objectwise total-to-pointwise left-derived comparisons as a natural
isomorphism and exposes its component computations.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The total left-derived functor, pulled back to the source, is naturally isomorphic to the
functor of its pointwise left-derived values. -/
@[stacks 05SA]
noncomputable def LeftDerived.Value.totalNatIso
    (F : C ⥤ D) (S : MorphismProperty C) [F.HasPointwiseLeftDerivedFunctor S] :
    S.Q ⋙ F.totalLeftDerived S.Q S ≅ LeftDerived.Value.functor F S :=
  LeftDerived.Value.modelNatIso F S (F.totalLeftDerived S.Q S)
    (F.totalLeftDerivedCounit S.Q S)

namespace LeftDerived.Value.totalNatIso

/-- The forward component of `LeftDerived.Value.totalNatIso` is the canonical objectwise
total-to-pointwise comparison. -/
@[simp, stacks 05SA "total left-derived value natural isomorphism computation"]
theorem hom_app (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.totalNatIso F S).hom.app X =
      (LeftDerived.Value.totalIso F S X).hom := sorry

/-- The inverse component of `LeftDerived.Value.totalNatIso` is the inverse objectwise
pointwise comparison. -/
@[simp, stacks 05SA "total left-derived value natural isomorphism computation"]
theorem inv_app (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.totalNatIso F S).inv.app X =
      (LeftDerived.Value.totalIso F S X).inv := sorry

end LeftDerived.Value.totalNatIso

end CategoryTheory.Functor
