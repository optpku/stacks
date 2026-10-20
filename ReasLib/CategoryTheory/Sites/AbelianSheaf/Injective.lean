/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectives under the abelian sheaf inclusion

Sheafification of abelian presheaves is an exact left adjoint. Its right adjoint
`sheafToPresheaf` therefore preserves injective objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The inclusion of abelian sheaves into abelian presheaves preserves injective objects. -/
@[stacks 03F6 "sheaf-to-presheaf preservation of injectives"]
instance sheafToPresheaf_preservesInjectiveObjects
    [HasSheafify J AddCommGrpCat.{max u v}] :
    (sheafToPresheaf J AddCommGrpCat.{max u v}).PreservesInjectiveObjects := sorry

/-- An injective abelian sheaf is injective as an abelian presheaf. -/
@[stacks 03F6 "injective abelian sheaf as a presheaf"]
theorem injective_toPresheaf [HasSheafify J AddCommGrpCat.{max u v}]
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : Injective F) :
    Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) := sorry

end CategoryTheory.Sheaf

namespace CategoryTheory.Functor

/-- Continuous pushforward of abelian sheaves preserves injective objects when the functor
between small sites preserves finite limits. -/
instance sheafPushforwardContinuous_preservesInjectiveObjects
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [Limits.HasFiniteLimits C] [Limits.PreservesFiniteLimits u] :
    (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).PreservesInjectiveObjects := sorry

end CategoryTheory.Functor
