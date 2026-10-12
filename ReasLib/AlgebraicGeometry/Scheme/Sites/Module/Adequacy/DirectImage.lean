/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.InjectiveResolution
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace SheafOfModules.IsAdequateWith

variable {S T : Scheme.{u}} {τ : StandardTopology}

/-- Pushforward along a quasi-compact and quasi-separated morphism preserves
adequacy for module sheaves on the standard big site. -/
theorem pushforward (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)}
    (hℱ : IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted ℱ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted
      ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ) := sorry

/-- Every higher direct image along a quasi-compact and quasi-separated morphism
preserves adequacy on the standard big site. -/
theorem higherDirectImage (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)}
    (hℱ : IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted ℱ) (i : ℕ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted
      (StandardTopology.Big.higherDirectImageModule τ f ℱ i) := sorry

end SheafOfModules.IsAdequateWith
