module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

variable (S : Scheme.{u}) (τ : StandardTopology)

/- Lemma 46.5.11 (1): adequate module sheaves form an abelian category. -/
@[stacks 06VQ] #check
  (@SheafOfModules.Adeq.instAbelian S τ :
    Abelian
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)))

/- Lemma 46.5.11 (2): the inclusion of adequate module sheaves is exact. -/
@[stacks 06VQ] #check
  (@SheafOfModules.Adeq.inclusionExact S τ :
    exactFunctor
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))
      (ObjectProperty.ι
        (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))))

/- Lemma 46.5.11 (3): adequacy is closed under short exact extensions. -/
@[stacks 06VQ] #check
  (@SheafOfModules.Adeq.instIsClosedUnderExtensions S τ :
    ObjectProperty.IsClosedUnderExtensions
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)))

/- Lemma 46.5.11 (4): adequate module sheaves have all small colimits and the inclusion preserves them. -/
@[stacks 06VQ] #check
  (@SheafOfModules.Adeq.instHasColimits S τ :
    HasColimits
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)))

/- Lemma 46.5.11 (5): the inclusion preserves all small colimits. -/
@[stacks 06VQ] #check
  (@SheafOfModules.Adeq.inclusionPreservesColimits S τ :
    PreservesColimits
      (ObjectProperty.ι
        (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))))

end SheafOfModules.Adeq
