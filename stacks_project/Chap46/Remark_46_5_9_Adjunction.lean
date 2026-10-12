/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Adjunction

/-!
# Compatibility checks for the adequate-module association and restriction API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Adeq

variable (S : Scheme.{u}) (τ : StandardTopology)

#check (smallZariskiPullback_mapsTo S τ :
  SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf .zariski S) ≤
    ObjectProperty.inverseImage
      (SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (Scheme.SiteRestriction.bigToZariski τ S).modulePullback)

#check (smallZariskiPushforward_mapsTo S τ :
  SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ) ≤
    ObjectProperty.inverseImage
      (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf .zariski S))
      (Scheme.SiteRestriction.bigToZariski τ S).modulePushforward)

#check (smallZariskiPullback S τ :
  (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory ⥤
    SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ))

#check (smallZariskiPushforward S τ :
  SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ) ⥤
    (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory)

#check (smallZariskiAdjunction S τ :
    smallZariskiPullback S τ ⊣ smallZariskiPushforward S τ)

#check (associated S τ :
    Scheme.QCoh S ⥤
      SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))

#check (zariskiRestriction S τ :
    SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) ⥤ Scheme.QCoh S)

#check (adjunction S τ : associated S τ ⊣ zariskiRestriction S τ)

#check (adjunctionUnitIsIso S τ : IsIso (adjunction S τ).unit)

end SheafOfModules.Adeq
