module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation

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

/-- An admissible functor represented by tensoring with an `A`-`B`-bimodule `K`
sends finitely presented right `A`-modules to finitely presented right `B`-modules
if and only if `K` is finitely presented as a right `B`-module. -/
theorem mapsFinitePresentation_iff
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (hF : Admissible R A B F)
    (hK : Nonempty (F ≅
      (@tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))) :
    ModuleCat.isFinitePresentation Aᵐᵒᵖ ≤
      (ModuleCat.isFinitePresentation Bᵐᵒᵖ).inverseImage F ↔
        Module.FinitePresentation Bᵐᵒᵖ K := sorry

end EilenbergWatts
end ModuleCat
