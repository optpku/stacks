module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open Module.Bimodule.RelativeTensor

universe u

namespace ModuleCat
namespace EilenbergWatts

variable {R A B K : Type u}
variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/- Remark 56.3.6: under the Eilenberg--Watts correspondence, `F` sends
finite right `A`-modules to finite right `B`-modules exactly when its
representing bimodule `K` is finite as a right `B`-module. -/
@[stacks 0GNY] #check
  (ModuleCat.EilenbergWatts.mapsFinite_iff :
    ∀ (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
      (hF : Admissible R A B F)
      (hK : Nonempty (F ≅
        (tensorModuleFunctor (R := R) (A := A) (B := B) K :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))),
      (∀ M : ModuleCat.{u} Aᵐᵒᵖ,
        Module.Finite Aᵐᵒᵖ M → Module.Finite Bᵐᵒᵖ (F.obj M)) ↔
        Module.Finite Bᵐᵒᵖ K)

end EilenbergWatts
end ModuleCat
