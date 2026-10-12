/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
public import ReasLib.CategoryTheory.Sites.Derived.Sections
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Declarations for this item will be appended below by the statement pipeline.

/- The source equation is represented by the canonical objectwise cohomology comparison in
ReasLib.  Its two factors are kept visible so downstream users can reuse either the cohomology
presheaf comparison or the derived-sections calculation independently. -/

universe u

/- 21.2.0.1: for an object `U` of the site and an injective resolution `I` of an abelian sheaf
`F`, the cohomology object `H^i(U, F)` is canonically isomorphic to the `i`-th homology of the
sections complex `Γ(U, I^•)`. -/
@[stacks 071C "cohomology over an object via an injective-resolution sections complex"]
#check fun {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    {F : Sheaf J AddCommGrpCat.{u}} (I : InjectiveResolution F) (U : C) (i : ℕ) =>
  (CategoryTheory.Sheaf.CohomologyPresheaf.appIso J F U i).symm ≪≫
    CategoryTheory.Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex J I U i

/- The reusable derived-sections calculation underlying the source-facing H′ view. -/
@[stacks 071C "derived inclusion and sections-complex comparison"]
#check @CategoryTheory.Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex
