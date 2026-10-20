module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

/-! # Global sections as morphisms from the constant integer sheaf -/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]

/-- The additive Hom functor represented by the constant integer sheaf. -/
abbrev globalSectionsHomFunctor :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  preadditiveCoyoneda.obj (op (constantIntegerSheaf J))

/-- The additive identification of lifted global sections with morphisms from the constant
integer sheaf is natural in the coefficient sheaf. -/
theorem globalSectionsHomIso_naturality
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) :
    ((Γ J AddCommGrpCat.{w}) ⋙ AddCommGrpCat.uliftFunctor.{max u w, w}).map f ≫
      (((AddEquiv.ulift : ULift.{max u w} ((Γ J AddCommGrpCat.{w}).obj G) ≃+
        (Γ J AddCommGrpCat.{w}).obj G).trans
      (globalSectionsAddEquivConstantIntegerSheafHomOnSite J G)).toAddCommGrpIso).hom =
    (((AddEquiv.ulift : ULift.{max u w} ((Γ J AddCommGrpCat.{w}).obj F) ≃+
      (Γ J AddCommGrpCat.{w}).obj F).trans
      (globalSectionsAddEquivConstantIntegerSheafHomOnSite J F)).toAddCommGrpIso).hom ≫
      (globalSectionsHomFunctor J).map f := sorry

/-- Global sections, lifted to the universe of sheaf morphisms, are naturally isomorphic to
morphisms from the constant integer sheaf. -/
def globalSectionsHomIso :
    (Γ J AddCommGrpCat.{w}) ⋙ AddCommGrpCat.uliftFunctor.{max u w, w} ≅
      globalSectionsHomFunctor J :=
  NatIso.ofComponents
    (fun F ↦ ((AddEquiv.ulift : ULift.{max u w} ((Γ J AddCommGrpCat.{w}).obj F) ≃+
      (Γ J AddCommGrpCat.{w}).obj F).trans
        (globalSectionsAddEquivConstantIntegerSheafHomOnSite J F)).toAddCommGrpIso)
    (fun f ↦ globalSectionsHomIso_naturality J f)

end CategoryTheory.Sheaf
