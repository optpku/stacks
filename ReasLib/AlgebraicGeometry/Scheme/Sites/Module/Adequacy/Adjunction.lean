/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction.Adequate
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Association and restriction for adequate modules

This module restricts the canonical pullback--pushforward adjunction from the
small Zariski site to the full categories of quasicoherent and adequate modules,
then transports it across the established small-site presentation of `Scheme.QCoh`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Adeq

variable (S : Scheme.{u}) (τ : StandardTopology)

/-- Pullback from the small Zariski site sends quasicoherent modules to adequate
modules on the big `τ`-site. -/
theorem smallZariskiPullback_mapsTo :
    SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf .zariski S) ≤
      ObjectProperty.inverseImage
        (SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))
        (Scheme.SiteRestriction.bigToZariski τ S).modulePullback := sorry

/-- Pushforward to the small Zariski site sends adequate modules to
quasicoherent modules. -/
theorem smallZariskiPushforward_mapsTo :
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) ≤
      ObjectProperty.inverseImage
        (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.smallStructureSheaf .zariski S))
        (Scheme.SiteRestriction.bigToZariski τ S).modulePushforward := sorry

/-- Pullback from small-Zariski quasicoherent modules to adequate modules on the
big `τ`-site. -/
noncomputable def smallZariskiPullback :
    (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory ⥤
      SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) :=
  ObjectProperty.FullSubcategory.restrict
    (Scheme.SiteRestriction.bigToZariski τ S).modulePullback
    (smallZariskiPullback_mapsTo S τ)

/-- The underlying object of `smallZariskiPullback` is the ambient ringed-site
module pullback. -/
theorem smallZariskiPullback_obj
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory) :
    ((smallZariskiPullback S τ).obj F).obj =
      (Scheme.SiteRestriction.bigToZariski τ S).modulePullback.obj F.obj := sorry

/-- Pushforward from adequate modules on the big `τ`-site to small-Zariski
quasicoherent modules. -/
noncomputable def smallZariskiPushforward :
    SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) ⥤
      (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (Scheme.SiteRestriction.bigToZariski τ S).modulePushforward
    (smallZariskiPushforward_mapsTo S τ)

/-- The underlying object of `smallZariskiPushforward` is the ambient ringed-site
module pushforward. -/
theorem smallZariskiPushforward_obj
    (G : SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ)) :
    ((smallZariskiPushforward S τ).obj G).obj =
      (Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.obj G.obj := sorry

/-- The pullback--pushforward adjunction restricted to small-Zariski
quasicoherent modules and adequate big-site modules. -/
noncomputable def smallZariskiAdjunction :
    smallZariskiPullback S τ ⊣ smallZariskiPushforward S τ :=
  ObjectProperty.FullSubcategory.adjunction
    (Scheme.SiteRestriction.bigToZariski τ S).modulePullback
    (Scheme.SiteRestriction.bigToZariski τ S).modulePushforward
    (Scheme.SiteRestriction.bigToZariski τ S).modulePullbackPushforwardAdjunction
    (smallZariskiPullback_mapsTo S τ) (smallZariskiPushforward_mapsTo S τ)

/-- The restricted Hom equivalence agrees with the ambient pullback--pushforward
Hom equivalence after forgetting the full-subcategory witnesses. -/
theorem smallZariskiAdjunction_homEquiv_hom
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf .zariski S)).FullSubcategory)
    (G : SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ))
    (f : (smallZariskiPullback S τ).obj F ⟶ G) :
    (((smallZariskiAdjunction S τ).homEquiv F G) f).hom =
      (((Scheme.SiteRestriction.bigToZariski τ S).modulePullbackPushforwardAdjunction
        ).homEquiv F.obj G.obj) f.hom := sorry

/-- The associated adequate module functor `F ↦ Fᵃ` on the big `τ`-site. -/
noncomputable def associated :
    Scheme.QCoh S ⥤
      SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) :=
  Scheme.AssociatedModule.smallFunctor .zariski S ⋙ smallZariskiPullback S τ

/-- The underlying big-site module of `associated.obj F` is isomorphic to the
canonical associated module `Fᵃ`. -/
theorem associated_obj_isomorphic (F : Scheme.QCoh S) :
    IsIsomorphic ((associated S τ).obj F).obj
      ((Scheme.AssociatedModule.bigModuleFunctor S τ).obj F) := sorry

/-- Restriction of an adequate big-site module to a quasicoherent module on
`S`. -/
noncomputable def zariskiRestriction :
    SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) ⥤ Scheme.QCoh S :=
  smallZariskiPushforward S τ ⋙
    (Scheme.AssociatedModule.smallFunctor .zariski S).asEquivalence.inverse

/-- Applying the small-Zariski associated-module functor after
`zariskiRestriction` recovers direct ringed-site pushforward up to isomorphism. -/
theorem zariskiRestriction_obj_isomorphic
    (G : SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ)) :
    IsIsomorphic
      ((Scheme.AssociatedModule.smallFunctor .zariski S).obj
        ((zariskiRestriction S τ).obj G)).obj
      ((Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.obj G.obj) := sorry

/-- The associated adequate module functor is left adjoint to small-Zariski
restriction. -/
noncomputable def adjunction : associated S τ ⊣ zariskiRestriction S τ :=
  (Scheme.AssociatedModule.smallFunctor .zariski S).asEquivalence.toAdjunction.comp
    (smallZariskiAdjunction S τ)

/-- The unit of the association--restriction adjunction is an isomorphism. -/
instance adjunctionUnitIsIso : IsIso (adjunction S τ).unit := sorry

end SheafOfModules.Adeq
