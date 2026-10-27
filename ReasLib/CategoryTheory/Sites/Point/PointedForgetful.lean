/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Category.Pointed
public import ReasLib.Algebra.Category.AddCommGrp.Pointed
public import ReasLib.CategoryTheory.Category.Pointed.Limits

/-!
# Coefficient change for point skyscrapers

Forgetting abelian coefficients induces the mate comparison between skyscrapers at any point of a site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Φ : Point.{w} J)
variable [LocallySmall.{w} C]
variable [J.HasSheafCompose AddCommGrpCat.toPointed]
variable [PreservesFilteredColimits AddCommGrpCat.toPointed]

/-- The mate comparing forgotten abelian skyscrapers with pointed skyscrapers. -/
def toPointedSkyscraperComparison :
    Φ.skyscraperSheafFunctor (A := AddCommGrpCat) ⋙
        sheafCompose J AddCommGrpCat.toPointed ⟶
      AddCommGrpCat.toPointed ⋙ Φ.skyscraperSheafFunctor (A := Pointed) :=
  mateEquiv (Φ.skyscraperSheafAdjunction (A := AddCommGrpCat))
    (Φ.skyscraperSheafAdjunction (A := Pointed))
    (Φ.sheafFiberCompIso AddCommGrpCat.toPointed).hom

/-- The coefficient-change comparison of skyscrapers is invertible. -/
theorem toPointedSkyscraperComparison_isIso :
    IsIso (toPointedSkyscraperComparison J Φ) := sorry

/-- The coefficient-change comparison as an isomorphism, using an explicit certificate. -/
def toPointedSkyscraperIso (h : IsIso (toPointedSkyscraperComparison J Φ)) :
    Φ.skyscraperSheafFunctor (A := AddCommGrpCat) ⋙
        sheafCompose J AddCommGrpCat.toPointed ≅
      AddCommGrpCat.toPointed ⋙ Φ.skyscraperSheafFunctor (A := Pointed) :=
  @asIso _ _ _ _ (toPointedSkyscraperComparison J Φ) h

/-- The forward map of `toPointedSkyscraperIso` is the mate comparison. -/
theorem toPointedSkyscraperIso_hom (h : IsIso (toPointedSkyscraperComparison J Φ)) :
    (toPointedSkyscraperIso J Φ h).hom = toPointedSkyscraperComparison J Φ := rfl

/-- The comparison satisfies the counit identity for the point skyscraper adjunction. -/
theorem toPointedSkyscraperComparison_counit (A : AddCommGrpCat) :
    Φ.sheafFiber (A := Pointed).map
        ((toPointedSkyscraperComparison J Φ).app A) ≫
      (Φ.skyscraperSheafAdjunction (A := Pointed)).counit.app
        (AddCommGrpCat.toPointed.obj A) =
    (Φ.sheafFiberCompIso AddCommGrpCat.toPointed).hom.app
        ((Φ.skyscraperSheafFunctor (A := AddCommGrpCat)).obj A) ≫
      AddCommGrpCat.toPointed.map
        ((Φ.skyscraperSheafAdjunction (A := AddCommGrpCat)).counit.app A) := sorry

end CategoryTheory.GrothendieckTopology.Point

end
