module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology.UnderlyingComparison
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology over a sheaf of sets on a ringed site

Module cohomology over a sheaf of sets is global cohomology after restriction to the associated
category-of-elements localization.  The comparison with the underlying additive sheaf is exposed
for both sheaves and presheaves of sets.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u v

namespace RingedSite.Localization.AtSheaf

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

/-- Module cohomology over a sheaf of sets, computed as global cohomology after restriction to
the category-of-elements localization. -/
@[stacks 079Y "localized module cohomology"]
abbrev moduleCohomology
    (R : Sheaf J RingCat.{max u v}) (K : Sheaf J (Type (max u v)))
    [HasExt (RingedSite.ModuleCat.{max u v} (site R K))]
    (F : SheafOfModules.{max u v} R) (p : ℕ) : AddCommGrpCat.{max u v} :=
  RingedSite.Hom.moduleGlobalCohomology
    (X := site R K)
    ((SheafOfModules.Localization.AtSheaf.restriction R K).obj F) p

-- The reported `sorryAx` is inherited only through the Prop-valued law fields of the canonical
-- `RingedSite.moduleCatAbelian` instance; the cohomology object itself is the existing `Ext` owner.

end RingedSite.Localization.AtSheaf

namespace SheafOfModules.Cohomology

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]
variable (R : Sheaf J RingCat.{max u v})

/-- Cohomology over a sheaf of sets of the underlying additive sheaf agrees with localized
module cohomology. -/
theorem underlyingOverSheaf_isomorphic
    (K : Sheaf J (Type (max u v)))
    [HasExt (RingedSite.ModuleCat.{max u v}
      (RingedSite.Localization.AtSheaf.site R K))]
    (F : SheafOfModules.{max u v} R) (p : ℕ) :
    IsIsomorphic
      (CategoryTheory.Sheaf.cohomologyOverSheaf K
        ((SheafOfModules.toSheaf R).obj F) p)
      (RingedSite.Localization.AtSheaf.moduleCohomology R K F p) := sorry

/-- Lemma 21.13.1 (079Y): cohomology over a presheaf of sets of the underlying additive sheaf
agrees with module cohomology after localizing at its sheafification. -/
@[stacks 079Y]
theorem underlyingOverPresheaf_isomorphic
    [HasSheafify J (Type (max u v))]
    (K : Cᵒᵖ ⥤ Type (max u v))
    [HasExt (RingedSite.ModuleCat.{max u v}
      (RingedSite.Localization.AtSheaf.site R
        ((presheafToSheaf J (Type (max u v))).obj K)))]
    (F : SheafOfModules.{max u v} R) (p : ℕ) :
    IsIsomorphic
      (CategoryTheory.Sheaf.cohomologyOverPresheaf K
        ((SheafOfModules.toSheaf R).obj F) p)
      (RingedSite.Localization.AtSheaf.moduleCohomology R
        ((presheafToSheaf J (Type (max u v))).obj K) F p) := sorry

end SheafOfModules.Cohomology
