module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Definition 46.5.7: the category of adequate `𝒪`-modules on `(Sch / S)_τ` is the full
subcategory `SheafOfModules.Adeq`; when the topology is suppressed, it is denoted `Adeq(S)`. -/
@[stacks 07AH]
#check (SheafOfModules.Adeq :
  {S : Scheme.{u}} → {τ : StandardTopology} →
    ((A : CommRingCat.{u}) → ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
    (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
      (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
        Under A ⥤ AddCommGrpCat.{u}) → Type (u + 1))
