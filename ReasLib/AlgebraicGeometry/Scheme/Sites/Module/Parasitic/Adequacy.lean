module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.DirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.DirectImage

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace SheafOfModules.IsAdequateWith

variable {S T : Scheme.{u}} {τ : StandardTopology}

/-- The pushforward of an adequate parasitic module sheaf along a
quasi-compact and quasi-separated morphism is adequate and parasitic. -/
theorem pushforwardParasitic (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)}
    (hAdequate : IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted ℱ)
    (hParasitic : SheafOfModules.IsParasiticOne ℱ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
        affineEvaluationUnderlyingLifted
        ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ) ∧
      SheafOfModules.IsParasiticOne
        ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ) := sorry

/-- Every higher direct image of an adequate parasitic module sheaf along a
quasi-compact and quasi-separated morphism is adequate and parasitic. -/
theorem higherDirectImageParasitic (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {ℱ : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ T)}
    (hAdequate : IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted ℱ)
    (hParasitic : SheafOfModules.IsParasiticOne ℱ) (i : ℕ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
        affineEvaluationUnderlyingLifted
        (StandardTopology.Big.higherDirectImageModule τ f ℱ i) ∧
      SheafOfModules.IsParasiticOne
        (StandardTopology.Big.higherDirectImageModule τ f ℱ i) := sorry

end SheafOfModules.IsAdequateWith
