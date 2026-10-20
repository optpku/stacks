/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.CommRingedRestriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

/-! # Exact inverse image from the small Zariski site to the small étale site -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.AssociatedModule
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Module inverse image from the small Zariski site to the small étale site is exact. -/
theorem commSmallEtaleToZariski_pullback_exact (X : Scheme.{u}) :
    exactFunctor
      (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .zariski X))
      (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X))
      (@modulePullback.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallCommRingedSite .etale X) (smallCommRingedSite .zariski X)
        (commSmallEtaleToZariski X)
        (commSmallEtaleToZariski_modulePushforward_isRightAdjoint X)) := sorry

/-- The canonical module inverse image between the small Zariski and étale sites,
bundled with its exactness. -/
def commSmallEtaleToZariskiExactPullback (X : Scheme.{u}) :
    RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .zariski X) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X) :=
  ⟨(@modulePullback.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallCommRingedSite .etale X) (smallCommRingedSite .zariski X)
        (commSmallEtaleToZariski X)
        (commSmallEtaleToZariski_modulePushforward_isRightAdjoint X)),
    commSmallEtaleToZariski_pullback_exact X⟩

/-- Exact inverse image from Zariski to étale derived module sheaves. -/
abbrev commSmallEtaleToZariskiDerived (X : Scheme.{u}) :
    ModuleDerived.{u + 1} (smallCommRingedSite .zariski X) ⥤
      ModuleDerived.{u + 1} (smallCommRingedSite .etale X) :=
  @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .zariski X)) inferInstance
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .zariski X))
    (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .zariski X))
    (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X)) inferInstance
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .etale X))
    (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .etale X))
    (commSmallEtaleToZariskiExactPullback X).obj
    (@modulePullback_additive.{u + 1, u + 1, u, u + 1, u, u + 1}
      (smallCommRingedSite .etale X) (smallCommRingedSite .zariski X)
      (commSmallEtaleToZariski X)
      (commSmallEtaleToZariski_modulePushforward_isRightAdjoint X))
    (commSmallEtaleToZariski_pullback_exact X).1
    (commSmallEtaleToZariski_pullback_exact X).2

/-- Derived Zariski-to-étale inverse image is induced by the exact module inverse image. -/
theorem commSmallEtaleToZariskiDerived_eq (X : Scheme.{u}) :
    commSmallEtaleToZariskiDerived X =
      @ExactFunctor.mapDerivedCategory
        (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .zariski X)) inferInstance
        (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1}
          (smallCommRingedSite .zariski X))
        (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .zariski X))
        (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X)) inferInstance
        (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1}
          (smallCommRingedSite .etale X))
        (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (smallCommRingedSite .etale X))
        (commSmallEtaleToZariskiExactPullback X) := rfl

end AlgebraicGeometry.Scheme.SiteRestriction
