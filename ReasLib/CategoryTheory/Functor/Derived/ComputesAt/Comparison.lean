module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computing Arbitrary Models of Derived Functors

This leaf relates the model-independent source predicate `ComputesAt` to the comparison map of
any chosen derived-functor model. The forward implications need only computation at the object;
the converses additionally retain the source-level `DefinedAt` condition. Both orientations are
provided so downstream applications do not have to replace a chosen model by Mathlib's total
derived functor.
-/

universe vC vD vH uC uD uH

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable (F : C ⥤ H) (S : MorphismProperty C) [S.ContainsIdentities]
variable (Q : C ⥤ D) [Q.IsLocalization S]

/-- Stacks 0BYZ: if `X` computes the right-derived value of `F`, then the comparison component
at `X` is invertible for every model of the right-derived functor. -/
@[stacks 0BYZ "right-derived comparison on a computing object"]
theorem RightDerived.ComputesAt.isIso_app
    (RF : D ⥤ H) (α : F ⟶ Q ⋙ RF) (X : C)
    (hX : RightDerived.ComputesAt F S X)
    (hRF : RF.IsRightDerivedFunctor α S) :
    IsIso (α.app X) := sorry

/-- Stacks 05SX: at an object where the source right-derived value is defined, computation is
equivalent to invertibility of the comparison component for any right-derived model. -/
@[stacks 05SX "right-derived comparison computation criterion"]
theorem RightDerived.DefinedAt.computesAt_iff_isIso_app
    (RF : D ⥤ H) (α : F ⟶ Q ⋙ RF) (X : C)
    (hX : RightDerived.DefinedAt F S X)
    (hRF : RF.IsRightDerivedFunctor α S) :
    RightDerived.ComputesAt F S X ↔ IsIso (α.app X) := sorry

/-- Stacks 05SX: if `X` computes the left-derived value of `F`, then the comparison component
at `X` is invertible for every model of the left-derived functor. -/
@[stacks 05SX "left-derived comparison on a computing object"]
theorem LeftDerived.ComputesAt.isIso_app
    (LF : D ⥤ H) (α : Q ⋙ LF ⟶ F) (X : C)
    (hX : LeftDerived.ComputesAt F S X)
    (hLF : LF.IsLeftDerivedFunctor α S) :
    IsIso (α.app X) := sorry

/-- Stacks 05SX: at an object where the source left-derived value is defined, computation is
equivalent to invertibility of the comparison component for any left-derived model. -/
@[stacks 05SX "left-derived comparison computation criterion"]
theorem LeftDerived.DefinedAt.computesAt_iff_isIso_app
    (LF : D ⥤ H) (α : Q ⋙ LF ⟶ F) (X : C)
    (hX : LeftDerived.DefinedAt F S X)
    (hLF : LF.IsLeftDerivedFunctor α S) :
    LeftDerived.ComputesAt F S X ↔ IsIso (α.app X) := sorry

end CategoryTheory.Functor
