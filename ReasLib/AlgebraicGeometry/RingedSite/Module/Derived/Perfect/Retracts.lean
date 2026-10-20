/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect

@[expose] public section

/-!
# Retracts of perfect derived module sheaves

This module registers the intrinsic perfectness predicate as stable under retracts. Generic
`ObjectProperty.IsStableUnderRetracts` APIs then provide direct-summand and biproduct consequences.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

section

/-- Lemma 21.47.8: perfect derived module sheaves on a ringed site are stable under retracts,
and hence under direct summands. -/
@[stacks 08GA]
instance isPerfect_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (IsPerfect : ObjectProperty (ModuleDerived.{w} X)) := sorry

end

section Biproducts

/-- Lemma 21.47.8: if a binary biproduct of derived module sheaves is perfect, then both
summands are perfect. -/
@[stacks 08GA]
theorem isPerfect_summands_of_biprod
    (K L : ModuleDerived.{w} X) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect := sorry

/-- The left summand of a perfect binary biproduct of derived module sheaves is perfect. -/
theorem isPerfect_left_of_biprod
    (K L : ModuleDerived.{w} X) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect := sorry

/-- The right summand of a perfect binary biproduct of derived module sheaves is perfect. -/
theorem isPerfect_right_of_biprod
    (K L : ModuleDerived.{w} X) (hKL : (K ⊞ L).IsPerfect) :
    L.IsPerfect := sorry

end Biproducts

end RingedSite.Hom.ModuleDerived
