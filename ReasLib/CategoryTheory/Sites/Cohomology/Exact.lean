module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Derived.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact sections and sheaf cohomology

This leaf records the site-generic consequence of exactness of the sections functor at one
object: all positive objectwise cohomology groups vanish.  The exactness hypothesis is kept on
the canonical `siteAbelianSectionsFunctor`, so topology-specific criteria can reuse the result
without rebuilding injective resolutions or derived-functor comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{max u v} C]

/-- Exactness of sections over `U` forces the next positive cohomology group to vanish. -/
@[stacks 0A3F "exact sections imply cohomology vanishing"]
theorem isZero_cohomology_succ_of_exactSections
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]
    (U : C)
    (hU : exactFunctor _ _ (siteAbelianSectionsFunctor J U))
    (F : Sheaf J AddCommGrpCat.{max u v}) (n : ℕ) :
    IsZero (F.H' (n + 1) U) := sorry

/-- Exactness of sections over `U` forces cohomology over `U` to vanish in every positive
degree. -/
@[stacks 0A3F "positive cohomology vanishing from exact sections"]
theorem isZero_cohomology_of_exactSections
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]
    (U : C)
    (hU : exactFunctor _ _ (siteAbelianSectionsFunctor J U))
    (F : Sheaf J AddCommGrpCat.{max u v}) {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q U) := sorry

/-- Exact sections at a terminal object force the next positive global cohomology group to
vanish. -/
@[stacks 0A3F "exact global sections imply cohomology vanishing"]
theorem isZero_globalCohomology_succ_of_exactSections
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]
    (T : C) (hT : IsTerminal T)
    (h_exact : exactFunctor _ _ (siteAbelianSectionsFunctor J T))
    (F : Sheaf J AddCommGrpCat.{max u v}) (n : ℕ) :
    IsZero ((functorH J (n + 1)).obj F) := sorry

/-- Exact sections at a terminal object force global cohomology to vanish in every positive
degree. -/
@[stacks 0A3F "positive global cohomology vanishing from exact sections"]
theorem isZero_globalCohomology_of_exactSections
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]
    (T : C) (hT : IsTerminal T)
    (h_exact : exactFunctor _ _ (siteAbelianSectionsFunctor J T))
    (F : Sheaf J AddCommGrpCat.{max u v}) {q : ℕ} (hq : 0 < q) :
    IsZero ((functorH J q).obj F) := sorry

end CategoryTheory.Sheaf
