/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module

@[expose] public section

open CategoryTheory
open CategoryTheory.Bimod
open Module.Bimodule.RelativeTensor

universe u

namespace ModuleCat
namespace EilenbergWatts

variable {R A B K : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/-- An admissible functor represented by a bimodule `K` is exact if and only if
the induced left `A`-module is flat. -/
theorem exact_iff_flat
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (hF : Admissible R A B F)
    (hK : Nonempty (F ≅
      (tensorModuleFunctor (R := R) (A := A) (B := B) K :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))) :
    exactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F ↔
      LeftModule.IsFlat (Module.Bimodule.toLeftModule (R := R) (A := A) K) := sorry

end EilenbergWatts
end ModuleCat
