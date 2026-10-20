/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangentCochain :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y),
    CochainComplex (CommModules X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.transitivityMap :
  ∀ {S : Scheme.{u}} {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B),
    pullbackCotangent p f ⟶ cotangent (p ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.toRelativeMap :
  ∀ {S : Scheme.{u}} {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B),
    cotangent (p ≫ f) ⟶ cotangent p)
