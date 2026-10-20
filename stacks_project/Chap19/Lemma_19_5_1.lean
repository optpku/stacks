/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace)

/- Lemma 19.5.1: sheaves of `𝒪_X`-modules have enough injectives. -/
@[stacks 01DI "enough injectives"] #check
  (inferInstance : EnoughInjectives X.Modules)

/- Lemma 19.5.1: sheaves of `𝒪_X`-modules admit functorial injective embeddings. -/
@[stacks 01DI "functorial injective embeddings"] #check
  (inferInstance : HasFunctorialInjectives X.Modules)

end AlgebraicGeometry.RingedSpace
