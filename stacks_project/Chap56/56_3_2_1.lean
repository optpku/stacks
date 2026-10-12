/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.ModuleFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace Module.Bimodule.RelativeTensor

variable {R A B : Type u} (K : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/- 56.3.2.1 -/
@[stacks 0GNU] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := A) (B := B) K :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)

end Module.Bimodule.RelativeTensor
