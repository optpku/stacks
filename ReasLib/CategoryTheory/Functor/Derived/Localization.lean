/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Functors of Functors Inverting a Localization Class

If a functor already inverts the chosen denominators, its localization lift is simultaneously a
left- and right-derived model. This leaf records model-independent uniqueness as
`IsIsomorphic`, avoiding a public choice of an isomorphism that depends on a derived-functor
proof witness.
-/

universe vC vD vH uC uD uH

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable (F : C ⥤ H) (W : MorphismProperty C)
variable (L : C ⥤ D) [L.IsLocalization W]

/-- Every right-derived model of a functor which already inverts the denominators is isomorphic
to its localization lift. -/
@[stacks 0BYW "right-derived model of an inverted functor"]
theorem IsRightDerivedFunctor.isIsomorphic_lift
    (hF : W.IsInvertedBy F) (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α W) :
    IsIsomorphic RF (Localization.lift F hF L) := sorry

/-- The total right-derived functor of a functor which already inverts the denominators is
isomorphic to its localization lift. -/
@[stacks 0BYW "total right-derived localization lift"]
theorem RightDerived.isIsomorphic_total_lift
    [F.HasRightDerivedFunctor W] (hF : W.IsInvertedBy F) :
    IsIsomorphic (F.totalRightDerived L W) (Localization.lift F hF L) := sorry

/-- The left-derived model of a functor which already inverts the denominators is isomorphic to
its localization lift. -/
@[stacks 0BYW "left-derived model of an inverted functor"]
theorem IsLeftDerivedFunctor.isIsomorphic_lift
    (hF : W.IsInvertedBy F) (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hLF : LF.IsLeftDerivedFunctor α W) :
    IsIsomorphic LF (Localization.lift F hF L) := sorry

/-- The total left-derived functor of a functor which already inverts the denominators is
isomorphic to its localization lift. -/
@[stacks 0BYW "total left-derived localization lift"]
theorem LeftDerived.isIsomorphic_total_lift
    [F.HasLeftDerivedFunctor W] (hF : W.IsInvertedBy F) :
    IsIsomorphic (F.totalLeftDerived L W) (Localization.lift F hF L) := sorry

end CategoryTheory.Functor
