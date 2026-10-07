module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Adequate

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Compatibility check for the shared parasitic object property on adequate module sheaves. -/
#check (SheafOfModules.Adeq.parasitic :
  {S : Scheme.{u}} → {τ : StandardTopology} →
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u}) →
    ObjectProperty (SheafOfModules.Adeq underline affineEvaluation))

/- Compatibility check for the membership specification of the parasitic property. -/
#check (SheafOfModules.Adeq.parasitic_iff :
  {S : Scheme.{u}} → {τ : StandardTopology} →
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u}) →
    (F : SheafOfModules.Adeq underline affineEvaluation) →
      SheafOfModules.Adeq.parasitic underline affineEvaluation F ↔
        SheafOfModules.IsParasiticOne F.obj)
