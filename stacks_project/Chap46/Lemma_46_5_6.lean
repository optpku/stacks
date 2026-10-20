module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Lemma 46.5.6 -/
@[stacks 06VL] #check (SheafOfModules.IsAdequate.extendedCech_acyclic :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ →
      (U V : Over S) → (g : V ⟶ U) → [IsAffine U.left] → [IsAffine V.left] →
      [Flat g.left] → [Surjective g.left] →
      (Arrow.Cech.extended (Arrow.mk g) ℱ.val.presheaf).Acyclic)

#check (SheafOfModules.IsAdequate.isSheaf_fpqc :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ →
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) ℱ.val.presheaf)

#check (SheafOfModules.IsAdequate.isSheaf_fppf :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ →
      Presheaf.IsSheaf (StandardTopology.fppf.overTopology S) ℱ.val.presheaf)

end SheafOfModules
