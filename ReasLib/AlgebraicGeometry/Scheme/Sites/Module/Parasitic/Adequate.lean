module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Sheaf

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- The object property selecting adequate module sheaves whose underlying module sheaf is
parasitic. -/
def parasitic
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u}) :
    ObjectProperty (Adeq underline affineEvaluation) :=
  fun F ↦ SheafOfModules.IsParasiticOne F.obj

/-- An adequate module sheaf is selected by `parasitic underline affineEvaluation` exactly
when its underlying module sheaf is parasitic. -/
theorem parasitic_iff
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u})
    (F : Adeq underline affineEvaluation) :
    parasitic underline affineEvaluation F ↔
      SheafOfModules.IsParasiticOne F.obj := sorry

end SheafOfModules.Adeq
