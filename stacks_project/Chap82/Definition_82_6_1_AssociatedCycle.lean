/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle :
  {S : Scheme.{u}} → {B X : AlgebraicSpace S} →
    [UniversallyCatenary B] → [IsQuasiSeparated B] →
    (f : X ⟶ B) → [QuasiSeparated f] → [LocallyOfFiniteType f] →
    (δ : Points B → ℤ) → [IsDimensionFunction δ] →
    (F : X.Modules) → [F.IsCoherent] → (k : ℤ) →
      AlgebraicGeometry.AlgebraicSpace.Hom.moduleSupportDeltaDimension f δ F ≤
        (k : EInt) → Function.locallyFinsupp (Points X) ℤ)
