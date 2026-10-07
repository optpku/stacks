module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear

/-!
# Composition of Eilenberg--Watts functors

This module owns the composite-kernel functor and the composition law for
Eilenberg--Watts correspondences.
-/

@[expose] public section

open CategoryTheory
open Module.Bimodule

universe u

namespace Module.Bimodule.RelativeTensor

variable {R A B C : Type u} (K K' : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [Ring C] [Algebra R C]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]
variable [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
variable [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
variable [SMulCommClass B Cᵐᵒᵖ K']

/-- The functor represented by the categorical balanced tensor of composable kernels `K` and `K'`. -/
noncomputable abbrev tensorCompositeFunctor :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ :=
  rightModuleFunctor (R := R) (A := A) ⋙
    CategoryTheory.Bimod.tensorRight
      ((toBimod (R := R) (A := A) (B := B) K).tensorBimod
        (toBimod (R := R) (A := B) (B := C) K')) ⋙
    (@rightModuleEquivalence R C _ _ _).inverse

/-- Sequential tensoring by `K` and `K'` is naturally isomorphic to the composite-kernel functor. -/
theorem tensorCompositeFunctor_iso :
    Nonempty (
      (@tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ) ⋙
        (@tensorModuleFunctor R B C K' _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ) ≅
      (@tensorCompositeFunctor R A B C K K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)) := sorry

end Module.Bimodule.RelativeTensor

namespace ModuleCat
namespace EilenbergWatts

variable {R A B C K K' : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [Ring C] [Algebra R C]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]
variable [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
variable [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
variable [SMulCommClass B Cᵐᵒᵖ K']

/-- Composable Eilenberg--Watts correspondences compose through the balanced tensor of kernels. -/
theorem tensorComposition
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (F' : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)
    (hF : Admissible R A B F)
    (hF' : Admissible R B C F')
    (hK : Nonempty (F ≅
      (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)))
    (hK' : Nonempty (F' ≅
      (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R B C K' _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ))) :
    Nonempty (F ⋙ F' ≅
      (@Module.Bimodule.RelativeTensor.tensorCompositeFunctor R A B C K K'
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)) := sorry

end EilenbergWatts
end ModuleCat
