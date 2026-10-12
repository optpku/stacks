/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.DirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 46.5.12 (1): for a quasi-compact and quasi-separated morphism, the
pushforward of an adequate module sheaf is adequate. -/
@[stacks 06VR] #check
  (SheafOfModules.IsAdequateWith.pushforward :
    ∀ {S T : Scheme.{u}} {τ : StandardTopology} (f : T ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsAdequateWith
          ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted ℱ →
        SheafOfModules.IsAdequateWith
          ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted
          ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ))

/- Lemma 46.5.12 (2): for a quasi-compact and quasi-separated morphism, every
higher direct image of an adequate module sheaf is adequate. -/
@[stacks 06VR] #check
  (SheafOfModules.IsAdequateWith.higherDirectImage :
    ∀ {S T : Scheme.{u}} {τ : StandardTopology} (f : T ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsAdequateWith
          ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted ℱ →
        ∀ (i : ℕ),
        SheafOfModules.IsAdequateWith
          ModuleValuedFunctor.tensorExtensionUnderlyingLifted
          SheafOfModules.affineEvaluationUnderlyingLifted
          (StandardTopology.Big.higherDirectImageModule τ f ℱ i))
