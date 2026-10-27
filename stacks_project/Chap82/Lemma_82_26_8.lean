/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.Commutation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

/- Lemma 82.26.8: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Then `c₁(L) ∈ A¹(X)` commutes with every element
`c ∈ Aᵖ(X)` in the operational Chow ring. -/
@[stacks 0ERR] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (L : X.Modules) [isInvertibleObject L]
      (p : ℤ) (c : OperationalChow δ f p),
      OperationalChow.homogeneous δ f 1 (OperationalFirstChern.degree f δ L) *
          OperationalChow.homogeneous δ f p c =
        OperationalChow.homogeneous δ f p c *
          OperationalChow.homogeneous δ f 1 (OperationalFirstChern.degree f δ L))
