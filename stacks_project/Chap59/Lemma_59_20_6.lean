module

public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (hfull : u.FullyFaithful)
variable [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasSheafify K AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
variable [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
variable [Limits.HasFiniteLimits C] [Limits.PreservesFiniteLimits u]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseRightKanExtension P]
variable (F' : Sheaf K AddCommGrpCat.{u}) (F : Sheaf J AddCommGrpCat.{u}) (U : C) (p : ℕ)

/- Lemma 59.20.6 (1) (03YY): cohomology over an object of a contained big site agrees with
cohomology computed in the larger site for a sheaf restricted along `u`. -/
@[stacks 03YY]
#check (CategoryTheory.SiteAbelianSectionsDerived.HPrime.objIso
  (u := u) p U F' :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F').H' p U ≅
      F'.H' p (u.obj U))

/- Lemma 59.20.6 (2) (03YY): every abelian sheaf on the contained big site extends to an abelian
sheaf on the larger big site. -/
@[stacks 03YY]
#check (CategoryTheory.Functor.FullyFaithful.exists_sheaf_extension
  (J := J) (K := K) (u := u) hfull F :
    ∃ F' : Sheaf K AddCommGrpCat.{u},
      Nonempty ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F' ≅ F))

end

end
