module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

/-- The composite from adequate module sheaves on the big `τ`-site of `Spec A`
to module presheaves, given by the adequate full-subcategory inclusion followed
by the canonical forgetful functor. -/
noncomputable abbrev toPresheaf
    (A : CommRingCat.{u})
    (τ : StandardTopology)
    (underline : (B : CommRingCat.{u}) →
      ModuleCat.{u} B ⥤ (Under B ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) →
        (B : CommRingCat.{u}) →
          (Scheme.Spec.obj (op B) ⟶ Scheme.Spec.obj (op A)) →
            Under B ⥤ AddCommGrpCat.{u}) :
    SheafOfModules.Adeq (S := Scheme.Spec.obj (op A)) (τ := τ)
        underline affineEvaluation ⥤
      _root_.PresheafOfModules.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))).structureSheaf.obj :=
  ObjectProperty.ι (SheafOfModules.IsAdequate underline affineEvaluation) ⋙
    SheafOfModules.forget
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))).structureSheaf

end SheafOfModules.Adeq
