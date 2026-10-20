/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.BivariantClass.gysin :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : L.sections),
    AlgebraicGeometry.BivariantClass δ
      (Over.homMk (AlgebraicGeometry.Scheme.zeroSchemeι L s) :
        Over.mk (AlgebraicGeometry.Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X) 1)
