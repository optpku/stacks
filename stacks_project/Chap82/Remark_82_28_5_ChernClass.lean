/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern

/-! Canonical rankwise Chern operations on the actual rational-equivalence quotient.
The implementation is the explicit Proj(Sym) / tautological / Segre construction.
No parallel cycle-as-Chow ring or chosen positive Chern family remains. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ),
    OperationalChow δ f (i : ℤ))
