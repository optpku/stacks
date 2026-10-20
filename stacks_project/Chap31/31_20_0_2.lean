module

import ReasLib.AlgebraicGeometry.RingedSpace.Module.Koszul
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- 31.20.0.2: A finite family `f` of global sections of `𝒪_X` determines the
Koszul complex `K_•(𝒪_X, f)`. -/
@[stacks 063A] #check
  (AlgebraicGeometry.RingedSpace.Koszul.complexOfSections :
    ∀ {X : RingedSpace} {n : ℕ},
      (Fin n → (SheafOfModules.unit X.ringCatSheaf).sections) → ChainComplex X.Modules ℕ)

#check @AlgebraicGeometry.RingedSpace.Koszul.sectionMap
