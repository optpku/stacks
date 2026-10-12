/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap56.Lemma_56_3_3
public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Exact
import StacksCheckRecall

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

/- Remark 56.3.5: in the Eilenberg--Watts situation of Lemma 56.3.3,
if `F` corresponds to `K`, then `F` is exact if and only if `K` is flat over `A`.
-/
@[stacks 0GNX] #check
  (ModuleCat.EilenbergWatts.exact_iff_flat :
    ∀ (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
      (hF : Admissible R A B F)
      (hK : Nonempty (F ≅
        (tensorModuleFunctor (R := R) (A := A) (B := B) K :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))),
      exactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F ↔
        LeftModule.IsFlat (Module.Bimodule.toLeftModule (R := R) (A := A) K))

end EilenbergWatts
end ModuleCat
