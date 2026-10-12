/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.FinitePresentation
public import stacks_project.Chap56.Lemma_56_3_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open Module.Bimodule.RelativeTensor

universe u

namespace ModuleCat
namespace EilenbergWatts

variable {R A B K : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/- Remark 56.3.7: in the Eilenberg--Watts situation, `F` sends finitely
presented right `A`-modules to finitely presented right `B`-modules if and
only if its corresponding `A`-`B`-bimodule `K` is finitely presented as a
right `B`-module. -/
@[stacks 0GNZ] #check
  (ModuleCat.EilenbergWatts.mapsFinitePresentation_iff :
    ∀ (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
      (hF : Admissible R A B F)
      (hK : Nonempty (F ≅
        (@tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))),
      ModuleCat.isFinitePresentation Aᵐᵒᵖ ≤
        (ModuleCat.isFinitePresentation Bᵐᵒᵖ).inverseImage F ↔
          Module.FinitePresentation Bᵐᵒᵖ K)

end EilenbergWatts
end ModuleCat
