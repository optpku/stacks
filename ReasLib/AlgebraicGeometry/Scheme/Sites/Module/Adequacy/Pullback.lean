/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S T : Scheme.{u}} {τ : StandardTopology}

namespace IsAdequate

/-- Pullback along a morphism of schemes preserves adequacy of module sheaves on
the standard big site with a fixed topology. -/
theorem pullback
    (f : T ⟶ S)
    {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
    (hℱ : IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying
      ((@RingedSite.Hom.modulePullback _ _ (StandardTopology.Big.pullbackRingedHom τ f)
        (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint τ f)).obj ℱ) := sorry

end IsAdequate

end SheafOfModules
