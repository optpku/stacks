/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain
public import ReasLib.CategoryTheory.Limits.Retract
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retracts of Pointwise Derived Domains

Pointwise right- and left-derived existence is a property of the localization-indexed diagram.
The colimit/limit retract API is therefore the canonical owner of its Karoubian closure.  This
leaf registers the resulting object-property instances; downstream transport along retracts and
binary-biproduct summands uses mathlib's generic `ObjectProperty.IsStableUnderRetracts` API.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.Definedness

/-- Stacks 05SD: in an idempotent-complete target, pointwise right-derived existence is stable
under retracts of source objects. -/
@[stacks 05SD "right pointwise derived retract stability"]
instance property.isStableUnderRetracts
    [IsIdempotentComplete D'] :
    (property F S).IsStableUnderRetracts := sorry

end Functor.RightDerived.Definedness

namespace Functor.LeftDerived.Definedness

/-- Stacks 05SD: in an idempotent-complete target, pointwise left-derived existence is stable
under retracts of source objects. -/
@[stacks 05SD "left pointwise derived retract stability"]
instance property.isStableUnderRetracts
    [IsIdempotentComplete D'] :
    (property F S).IsStableUnderRetracts := sorry

end Functor.LeftDerived.Definedness

end CategoryTheory
