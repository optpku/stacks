/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.CategoryTheory.Sites.FilteredColimit.GlobalSections
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented module sheaves and filtered colimits

This file separates the internal-Hom comparison from the global-Hom consequence.  The former is
local to module sheaves; the latter additionally uses the quasi-compact test-set criterion for
global sections.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed Opposite

noncomputable section

universe u v w

namespace SheafOfModules.IsFinitePresentation.FilteredColimit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{max u v}}
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section InternalHom

variable {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
variable [MonoidalCategory (SheafOfModules.{max u v} R)]
variable [MonoidalClosed (SheafOfModules.{max u v} R)]

/-- The canonical filtered-colimit comparison for internal Hom out of `F`. -/
@[stacks 0GMZ "internal-Hom comparison"]
noncomputable abbrev ihomComparison
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)] :
    colimit (G ⋙ ihom F) ⟶ (ihom F).obj (colimit G) :=
  colimit.post G (ihom F)

/-- Lemma 18.27.11 (0GMZ): internal Hom from a finitely presented module sheaf commutes with a
filtered colimit. -/
@[stacks 0GMZ, instance]
theorem ihom_isIso
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)] :
    IsIso (ihomComparison F G) := sorry

/-- The internal-Hom comparison is characterized on each colimit coprojection. -/
@[reassoc (attr := simp), stacks 0GMZ "internal-Hom comparison coprojection"]
theorem ihomComparison_ι
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)] (i : Λ) :
    colimit.ι (G ⋙ ihom F) i ≫ ihomComparison F G =
      (ihom F).map (colimit.ι G i) := sorry

/-- The inverse of the filtered-colimit internal-Hom comparison. -/
@[stacks 0GMZ "internal-Hom comparison inverse"]
noncomputable def ihomComparisonInv
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    (ihom F).obj (colimit G) ⟶ colimit (G ⋙ ihom F) :=
  inv (ihomComparison F G)

/-- The internal-Hom comparison followed by its named inverse is the identity. -/
@[simp, stacks 0GMZ "internal-Hom comparison forward-inverse law"]
theorem ihomComparison_hom_inv_id
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    ihomComparison F G ≫ ihomComparisonInv F G = 𝟙 _ := sorry

/-- The inverse internal-Hom comparison followed by the comparison is the identity. -/
@[simp, stacks 0GMZ "internal-Hom comparison inverse-forward law"]
theorem ihomComparison_inv_hom_id
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    ihomComparisonInv F G ≫ ihomComparison F G = 𝟙 _ := sorry

/-- The filtered-colimit internal-Hom comparison bundled with its named inverse. -/
@[stacks 0GMZ "internal-Hom comparison isomorphism"]
noncomputable def ihomComparisonIso
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    colimit (G ⋙ ihom F) ≅ (ihom F).obj (colimit G) where
  hom := ihomComparison F G
  inv := ihomComparisonInv F G
  hom_inv_id := ihomComparison_hom_inv_id F G
  inv_hom_id := ihomComparison_inv_hom_id F G

/-- The forward map of the filtered-colimit internal-Hom isomorphism. -/
@[simp, stacks 0GMZ "internal-Hom comparison isomorphism hom"]
theorem ihomComparisonIso_hom
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    (ihomComparisonIso F G).hom = ihomComparison F G := sorry

/-- The inverse map of the filtered-colimit internal-Hom isomorphism. -/
@[simp, stacks 0GMZ "internal-Hom comparison isomorphism inverse"]
theorem ihomComparisonIso_inv
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ ihom F)]
    [IsIso (ihomComparison F G)] :
    (ihomComparisonIso F G).inv = ihomComparisonInv F G := sorry

end InternalHom

section GlobalHom

variable [HasWeakSheafify J (Type (max u v))]

/-- The canonical filtered-colimit comparison for represented Hom out of `F`. -/
@[stacks 0GN0 "represented-Hom comparison"]
noncomputable abbrev homComparison
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))] :
    colimit (G ⋙ coyoneda.obj (op F)) ⟶ (coyoneda.obj (op F)).obj (colimit G) :=
  colimit.post G (coyoneda.obj (op F))

/-- Lemma 18.27.12 (0GN0): under the quasi-compact test-set hypothesis, Hom from a finitely
presented module sheaf preserves filtered colimits. -/
@[stacks 0GN0 "preservation"]
theorem preservesHom_of_testSet
    (hJ : GrothendieckTopology.QuasiCompact.HasTestSet J)
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation] :
    PreservesFilteredColimits (coyoneda.obj (op F)) := sorry

/-- Lemma 18.27.12 (0GN0), canonical owner form: under the quasi-compact test-set hypothesis, a
finitely presented module sheaf is finitely presentable as an object of its module category. -/
@[stacks 0GN0 "finitely presentable object"]
theorem isFinitelyPresentable_of_testSet
    (hJ : GrothendieckTopology.QuasiCompact.HasTestSet J)
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation] :
    IsFinitelyPresentable.{max u v} F := sorry

/-- The fixed-diagram form of Lemma 18.27.12: the canonical colimit-to-Hom comparison is an
isomorphism. -/
@[stacks 0GN0 "fixed diagram"]
theorem hom_isIso_of_testSet
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (hJ : GrothendieckTopology.QuasiCompact.HasTestSet J)
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))] :
    IsIso (homComparison F G) := sorry

/-- The represented-Hom comparison is characterized on each colimit coprojection. -/
@[reassoc (attr := simp), stacks 0GN0 "represented-Hom comparison coprojection"]
theorem homComparison_ι
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))] (i : Λ) :
    colimit.ι (G ⋙ coyoneda.obj (op F)) i ≫ homComparison F G =
      (coyoneda.obj (op F)).map (colimit.ι G i) := sorry

/-- The test-set criterion registered as the canonical `IsIso` instance for represented Hom. -/
@[stacks 0GN0 "represented-Hom comparison instance", instance]
theorem hom_isIso_of_testSet_inst
    [GrothendieckTopology.QuasiCompact.HasTestSet J]
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))] :
    IsIso (homComparison F G) := sorry

/-- The inverse of the represented-Hom filtered-colimit comparison. -/
@[stacks 0GN0 "represented-Hom comparison inverse"]
noncomputable def homComparisonInv
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    (coyoneda.obj (op F)).obj (colimit G) ⟶ colimit (G ⋙ coyoneda.obj (op F)) :=
  inv (homComparison F G)

/-- The represented-Hom comparison followed by its named inverse is the identity. -/
@[simp, stacks 0GN0 "represented-Hom comparison forward-inverse law"]
theorem homComparison_hom_inv_id
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    homComparison F G ≫ homComparisonInv F G = 𝟙 _ := sorry

/-- The inverse represented-Hom comparison followed by the comparison is the identity. -/
@[simp, stacks 0GN0 "represented-Hom comparison inverse-forward law"]
theorem homComparison_inv_hom_id
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    homComparisonInv F G ≫ homComparison F G = 𝟙 _ := sorry

/-- The represented-Hom filtered-colimit comparison bundled with its named inverse. -/
@[stacks 0GN0 "represented-Hom comparison isomorphism"]
noncomputable def homComparisonIso
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    colimit (G ⋙ coyoneda.obj (op F)) ≅
      (coyoneda.obj (op F)).obj (colimit G) where
  hom := homComparison F G
  inv := homComparisonInv F G
  hom_inv_id := homComparison_hom_inv_id F G
  inv_hom_id := homComparison_inv_hom_id F G

/- The projection lemmas below keep the named comparison API stable under `Iso` unfolding. -/
/-- The forward map of the represented-Hom filtered-colimit isomorphism. -/
@[simp, stacks 0GN0 "represented-Hom comparison isomorphism hom"]
theorem homComparisonIso_hom
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    (homComparisonIso F G).hom = homComparison F G := sorry

/-- The inverse map of the represented-Hom filtered-colimit isomorphism. -/
@[simp, stacks 0GN0 "represented-Hom comparison isomorphism inverse"]
theorem homComparisonIso_inv
    {Λ : Type (max u v)} [SmallCategory Λ] [IsFiltered Λ]
    (F : SheafOfModules.{max u v} R) [F.IsFinitePresentation]
    (G : Λ ⥤ SheafOfModules.{max u v} R)
    [HasColimit G] [HasColimit (G ⋙ coyoneda.obj (op F))]
    [IsIso (homComparison F G)] :
    (homComparisonIso F G).inv = homComparisonInv F G := sorry

end GlobalHom

end SheafOfModules.IsFinitePresentation.FilteredColimit
