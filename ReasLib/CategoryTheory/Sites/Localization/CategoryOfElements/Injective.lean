/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.InverseImage
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective abelian sheaves on category-of-elements localizations

The inverse-image functor for a category-of-elements localization preserves injective abelian
sheaves.  The functorial instance is the canonical owner; the objectwise theorem is an
explicit-evidence bridge for callers that do not want to install a temporary instance.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Sheaf.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Lemma 21.13.3 (1): inverse image along the category-of-elements localization preserves
injective abelian sheaves. -/
@[stacks 07A0 "(1), localization inverse image preserves injectives", instance]
instance inverseImage_preservesInjectiveObjects (K : Sheaf J (Type v)) :
    (inverseImage K AddCommGrpCat.{v}).PreservesInjectiveObjects := sorry

/-- Objectwise form of preservation of injectives by category-of-elements localization. -/
@[stacks 07A0 "(1), inverse image of an injective abelian sheaf"]
theorem injective_inverseImage (K : Sheaf J (Type v))
    {F : Sheaf J AddCommGrpCat.{v}} (hF : Injective F) :
    Injective ((inverseImage K AddCommGrpCat.{v}).obj F) := sorry

end CategoryTheory.Sheaf.Localization
