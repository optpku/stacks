/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.EtaleRestriction

/-!
# Exact derived pullback along ε

The canonical commutative small Zariski-to-étale restriction induces exact
inverse image on unbounded derived categories of module sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open RingedSite.Hom

universe u

#check (AlgebraicGeometry.Scheme.SiteRestriction.commSmallEtaleToZariskiDerived :
  ∀ X : Scheme.{u}, ModuleDerived.{u + 1} (smallCommRingedSite .zariski X) ⥤
    ModuleDerived.{u + 1} (smallCommRingedSite .etale X))

#check (AlgebraicGeometry.Scheme.SiteRestriction.commSmallEtaleToZariskiDerived_eq :
  ∀ X : Scheme.{u}, commSmallEtaleToZariskiDerived X =
    @ExactFunctor.mapDerivedCategory
      (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .zariski X)) inferInstance
      (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1}
        (smallCommRingedSite .zariski X))
      (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
        (smallCommRingedSite .zariski X))
      (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X)) inferInstance
      (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1}
        (smallCommRingedSite .etale X))
      (moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
        (smallCommRingedSite .etale X))
      (commSmallEtaleToZariskiExactPullback X))
