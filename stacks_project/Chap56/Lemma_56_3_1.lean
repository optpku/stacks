module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Module.Bimodule.RelativeTensor

namespace ModuleCat

/- Lemma 56.3.1: for rings `A` and `B` and a functor `F` between their
right-module categories, the tensor-functor, right-exact/direct-sum,
cocontinuity, and existence-of-a-right-adjoint conditions are equivalent. -/
@[stacks 0GNS] #check (ModuleCat.EilenbergWatts.eilenbergWatts_tfae :
    ∀ {A B : Type} [Ring A] [Ring B],
    (F : ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ) →
    List.TFAE
      [ ∃ (K : Type) (_ : AddCommGroup K) (_ : Module A K)
            (_ : Module Bᵐᵒᵖ K) (_ : SMulCommClass A Bᵐᵒᵖ K),
          Nonempty (F ≅
            @tensorModuleFunctor ℤ A B K _ _ _ _ _ _ _ _ _ _ _ _)
      , rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F ∧
          ∀ J : Type, PreservesColimitsOfShape (Discrete J) F
      , PreservesColimits F
      , F.IsLeftAdjoint ])

end ModuleCat
