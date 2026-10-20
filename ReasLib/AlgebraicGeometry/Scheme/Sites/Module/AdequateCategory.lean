module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- The full subcategory of module sheaves adequate for the specified extension and affine-evaluation data. -/
abbrev Adeq
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u}) :=
  ObjectProperty.FullSubcategory (IsAdequate underline affineEvaluation)

namespace Adeq

/-- Every object of the adequate module-sheaf category satisfies the adequacy property. -/
theorem isAdequate
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u})
    (ℱ : Adeq underline affineEvaluation) :
    IsAdequate underline affineEvaluation ℱ.obj := sorry

end Adeq

end SheafOfModules
