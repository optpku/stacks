/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern

/-! # Comparison of the index-one Chern class with first Chern intersection -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (L : X.Modules) [isInvertibleObject L]

/-- The index-one Chern class of an invertible module is its operational first Chern class. -/
theorem chernClass_eq : ChernClass.chernClass δ f L 1 = degree f δ L := sorry

/-- The index-one Chern cap of an invertible module agrees with first Chern intersection on every good test space. -/
theorem chernClass_cap_eq {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (ChernClass.chernClass δ f L 1).cap g k = (degree f δ L).cap g k := sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
