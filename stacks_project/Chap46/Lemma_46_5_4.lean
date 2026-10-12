/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 46.5.4 -/
@[stacks 06VJ] #check (SheafOfModules.IsAdequate.pullback :
    ∀ {S T : Scheme.{u}} {τ : StandardTopology}
      (f : T ⟶ S)
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ →
      SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying
        ((@RingedSite.Hom.modulePullback _ _
          (StandardTopology.Big.pullbackRingedHom τ f)
          (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint τ f)).obj ℱ))
