/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The compatibility import exposes arbitrary derived pullback preservation with the
source-facing aliases. -/
#check (pullback.mapsTo :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage
        (RingedSpace.modulePullbackDerived f.toLRSHom.toShHom))

end AlgebraicGeometry.Scheme.DerivedQCoh
