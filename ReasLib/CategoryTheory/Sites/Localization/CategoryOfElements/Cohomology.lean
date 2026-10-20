/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Ext
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.Injective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology on a category-of-elements localization

Cohomology over a sheaf of sets is identified with global cohomology after inverse image to its
category-of-elements localization.  The localized cohomology object is named separately so
downstream statements do not repeat the site and inverse-image construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (K : Sheaf J (Type v))
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt (Sheaf J AddCommGrpCat.{v})]
variable [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]

/-- Global cohomology after inverse image to the category-of-elements localization of `K`. -/
@[stacks 07A0 "(2), cohomology on the category-of-elements localization"]
abbrev cohomology (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (((inverseImage K AddCommGrpCat.{v}).obj F).H p)

/-- Lemma 21.13.3 (2): cohomology over `K` is isomorphic to global cohomology after inverse
image to the category-of-elements localization of `K`. -/
@[stacks 07A0 "(2), cohomology comparison"]
theorem cohomologyOverSheaf_isomorphic
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    IsIsomorphic (cohomologyOverSheaf K F p) (cohomology K F p) := sorry

end CategoryTheory.Sheaf.Localization
