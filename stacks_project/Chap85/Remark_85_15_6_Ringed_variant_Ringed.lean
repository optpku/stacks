module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Family
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe ι u v w z

variable {X : RingedSite.{u, v, w}}

/- Remark 85.15.6 (Ringed variant): restriction and gluing give the product
decomposition of module sheaves on a ringed family localization. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.modulesEquiv :
  ∀ K : FormalCoproduct.{ι} X.carrier,
    SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K) ≌
      ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))
