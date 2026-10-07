module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Adequacy

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 46.6.3 (1) -/
@[stacks 06ZP] #check
  (SheafOfModules.IsAdequateWith.pushforwardParasitic :
    ∀ {S T : Scheme.{u}} {τ : StandardTopology} (f : T ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
        SheafOfModules.affineEvaluationUnderlyingLifted ℱ →
      SheafOfModules.IsParasiticOne ℱ →
      SheafOfModules.IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted
          ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ) ∧
        SheafOfModules.IsParasiticOne
          ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ))

/- Lemma 46.6.3 (2) -/
@[stacks 06ZP] #check
  (SheafOfModules.IsAdequateWith.higherDirectImageParasitic :
    ∀ {S T : Scheme.{u}} {τ : StandardTopology} (f : T ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
        SheafOfModules.affineEvaluationUnderlyingLifted ℱ →
      SheafOfModules.IsParasiticOne ℱ → (i : ℕ) →
      SheafOfModules.IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted
          (StandardTopology.Big.higherDirectImageModule τ f ℱ i) ∧
        SheafOfModules.IsParasiticOne
          (StandardTopology.Big.higherDirectImageModule τ f ℱ i))
