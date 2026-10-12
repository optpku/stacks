/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEvaluation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Lemma 46.5.2 -/
@[stacks 06VI] #check (SheafOfModules.IsAdequate.affineEvaluation :
    ∀ {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ →
      (A : CommRingCat.{u}) → (f : Scheme.Spec.obj (op A) ⟶ S) →
        Adequate A (ModuleValuedFunctor.tensorExtensionUnderlying A)
          (SheafOfModules.affineEvaluationUnderlying ℱ A f))

end SheafOfModules
