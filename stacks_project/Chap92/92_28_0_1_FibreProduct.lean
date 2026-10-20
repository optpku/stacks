/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.cone :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
    DerivedCategory (CommModules (pullback f g)))

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.coneInr :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
    cotangent (toBase f g) ⟶ cone f g)
