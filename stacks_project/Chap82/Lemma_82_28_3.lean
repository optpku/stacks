/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernComparison

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open AlgebraicGeometry.AlgebraicSpace.OperationalChow

universe u

/- Lemma 82.28.3: The first Chern class of an invertible module equals its operational first Chern class. -/
@[stacks 0ES0] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.chernClass_eq :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L],
      ChernClass.chernClass δ f L 1 = OperationalFirstChern.degree f δ L)

#check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.chernClass_cap_eq :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      (ChernClass.chernClass δ f L 1).cap g k = (OperationalFirstChern.degree f δ L).cap g k)
