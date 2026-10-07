module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
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
