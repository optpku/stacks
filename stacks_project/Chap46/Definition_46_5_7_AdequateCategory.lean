module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Compatibility checks for the shared adequate module-sheaf category. -/
#check (SheafOfModules.Adeq :
  {S : Scheme.{u}} → {τ : StandardTopology} →
    ((A : CommRingCat.{u}) → ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
    (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
      (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
        Under A ⥤ AddCommGrpCat.{u}) → Type (u + 1))

#check (SheafOfModules.Adeq.isAdequate :
  {S : Scheme.{u}} → {τ : StandardTopology} →
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
      (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
        Under A ⥤ AddCommGrpCat.{u}) →
    (ℱ : SheafOfModules.Adeq (S := S) (τ := τ) underline affineEvaluation) →
      SheafOfModules.IsAdequate underline affineEvaluation ℱ.obj)
