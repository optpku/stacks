module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
public import ReasLib.CategoryTheory.Sites.Derived.Sections
import StacksCheckRecall

@[expose] public section

/- 20.2.0.3: the cohomology of a sheaf on an object is computed by the corresponding sections
complex of an injective resolution.  The tagged check retains the objectwise sheaf semantics;
the generic injective-resolution owner is checked separately. -/

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory.Sheaf

@[stacks 0714 "sheaf cohomology from an injective resolution"]
#check fun {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    {F : Sheaf J AddCommGrpCat.{u}} (I : InjectiveResolution F) (X : C) (i : ℕ) =>
  (CohomologyPresheaf.appIso J F X i).symm ≪≫
    rightDerivedInclusion_app_obj_iso_homology_sections_complex J I X i

#check @CategoryTheory.InjectiveResolution.isoRightDerivedObj

end CategoryTheory.Sheaf

end
