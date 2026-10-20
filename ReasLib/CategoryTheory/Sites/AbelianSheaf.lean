/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective

/-!
# Abelian Sheaves on a Site

This module owns the category of sheaves of abelian groups on a Grothendieck site and its
canonical abelian-category structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/-- Sheafification exists for abelian presheaves with coefficients in the universe
containing the objects and morphisms of the site. -/
instance AbelianSheaf.hasSheafify (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{max u v} :=
  @CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
    _ _ J AddCommGrpCat.{max u v} inferInstance
    (fun _ _ _ => inferInstance) (fun _ => inferInstance)
    _ _ inferInstance inferInstance
    (fun U => @Limits.PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
      (CategoryTheory.forget AddCommGrpCat.{max u v})
      AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
      (J.Cover U)ᵒᵖ inferInstance
      (@isFiltered_op_of_isCofiltered _ _
        (@isCofiltered_of_semilatticeInf_nonempty _ inferInstance ⟨⊤⟩)))
    inferInstance
    (fun _ => inferInstance) inferInstance inferInstance (fun _ => small_self _)

/-- The category of sheaves of abelian groups on a Grothendieck site. -/
abbrev SiteAbelianSheafCat (J : GrothendieckTopology C) :=
  Sheaf J AddCommGrpCat.{max u v}

/-- Sheaves of abelian groups on a site form an abelian category. -/
instance sheafAddCommGrpCat_abelian (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}] :
    Abelian (SiteAbelianSheafCat J) :=
  sheafIsAbelian

end

end CategoryTheory
