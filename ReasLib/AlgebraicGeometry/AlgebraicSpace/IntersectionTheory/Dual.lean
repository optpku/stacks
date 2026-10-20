/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Dual
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern

/-!
# Chern classes of dual modules on algebraic spaces

On a good algebraic space, the degree-`i` Chern class of the dual
of a finite locally free module is `(-1) ^ i` times its degree-`i` Chern class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- On a good algebraic space over a universally catenary quasi-separated base,
the degree-`i` Chern class of the canonical dual of a finite locally free module
is `(-1)^i` times the degree-`i` Chern class of that module. -/
theorem chernClass_dual {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    chernClass δ f (Modules.dual E) i = ((-1 : ℤ) ^ i) • chernClass δ f E i := sorry

/-- Capping with the Chern class of the canonical dual is multiplication by
`(-1)^i` of capping with the original Chern class. -/
theorem chernClass_dual_cap {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f (Modules.dual E) i).cap g k =
      ((-1 : ℤ) ^ i) • (chernClass δ f E i).cap g k := sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
