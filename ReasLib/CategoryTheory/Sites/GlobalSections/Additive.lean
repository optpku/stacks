/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Preadditive.Limits

/-!
# Additivity of Global Sections

This leaf exposes the canonical additive structure on global sections of
abelian-group-valued sheaves.  The right-adjoint formulation is used so the
API does not impose an unrelated large-limit hypothesis on a site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]

/-- Global sections of abelian-group-valued sheaves are additive whenever the global sections
functor exists. -/
@[stacks 0D6H "additivity of abelian-sheaf global sections"]
instance globalSections_additive
    (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}] :
    (Γ J AddCommGrpCat.{w}).Additive := sorry

end CategoryTheory.Sheaf
