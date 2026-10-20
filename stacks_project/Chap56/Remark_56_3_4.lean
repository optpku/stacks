module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 56.3.4: composable Eilenberg--Watts kernels correspond to the composite functor. -/
@[stacks 0GNW] #check
  (ModuleCat.EilenbergWatts.tensorComposition :
    ∀ {R A B C K K' : Type u}
      [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
      [Ring C] [Algebra R C]
      [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
      [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
      [SMulCommClass A Bᵐᵒᵖ K]
      [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
      [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
      [SMulCommClass B Cᵐᵒᵖ K']
      (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
      (F' : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)
      (hF : ModuleCat.EilenbergWatts.Admissible R A B F)
      (hF' : ModuleCat.EilenbergWatts.Admissible R B C F')
      (hK : Nonempty (F ≅
        (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)))
      (hK' : Nonempty (F' ≅
        (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R B C K' _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)))
      , Nonempty (F ⋙ F' ≅
        (@Module.Bimodule.RelativeTensor.tensorCompositeFunctor R A B C K K'
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :
          ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)))

/- Remark 56.3.4, as data: the canonical identification of `F ⋙ F'` with tensoring by the
balanced tensor `K ⊗_B K'`, built from given identifications `F ≅ - ⊗_A K` and `F' ≅ - ⊗_B K'`. -/
@[stacks 0GNW] #check
  (ModuleCat.EilenbergWatts.tensorCompositionIso :
    ∀ {R A B C : Type u} {K K' : Type u}
      [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
      [Ring C] [Algebra R C]
      [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
      [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
      [SMulCommClass A Bᵐᵒᵖ K]
      [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
      [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
      [SMulCommClass B Cᵐᵒᵖ K']
      {F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ}
      {F' : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ},
      (F ≅ Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := A) (B := B) K) →
      (F' ≅ Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := B) (B := C) K') →
      (F ⋙ F' ≅
        Module.Bimodule.RelativeTensor.tensorCompositeFunctor
          (R := R) (A := A) (B := B) (C := C) K K'))
