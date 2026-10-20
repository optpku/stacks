/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.SmallEtale

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SmallEtale.inclusion :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.DerivedQCoh.SmallEtale X ⥤
        DerivedCategory
          (RingedSite.ModuleCat.{u} (AlgebraicGeometry.Scheme.Etale.Small.ringedSite X)))
