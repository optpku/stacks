/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open scoped BigOperators

universe u

/- Definition 82.28.2 (1): In Situation 82.2.1 let `X / B` be good. Let `E`
be a finite locally free `𝒪_X`-module of rank `r`. For
`i = 0, …, r` the `i`th Chern class of `E` is the bivariant class
`c_i(E) ∈ A^i(X)` of degree `i` constructed in Lemma 82.28.1. -/
@[stacks 0ERZ] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.degreeOfRank :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      (i : ℕ) (hi : i ≤ r),
      OperationalChow δ f i)

/- Definition 82.28.2 (2): The total Chern class of `E` is the formal sum
`c(E) = c_0(E) + … + c_r(E)`, viewed as a nonhomogeneous bivariant class
on `X`. -/
@[stacks 0ERZ] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.totalOfRank :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E],
      OperationalChow.ring δ f)
