module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension.Serre
import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
import stacks_project.Chap42.Situation_42_7_1

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Lemma 42.23.1: for a scheme locally of finite type over a universally catenary scheme,
coherent sheaves whose relative `δ`-support dimension is at most `k` form a Serre subcategory. -/
@[stacks 02S8] #check
  (AlgebraicGeometry.RingedSpace.Coh.supportDimensionLEIsSerreClass
      (X := X.toRingedSpace) (f.relativeDimensionFunction δ) k :
    (AlgebraicGeometry.RingedSpace.Coh.supportDimensionLE
      (f.relativeDimensionFunction δ) k).IsSerreClass)

end AlgebraicGeometry.Scheme.Modules
