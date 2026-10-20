/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian

/-!
# Chern classes of a short exact sequence with a trivial submodule
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- The top operational Chern class vanishes for a short exact sequence with a
trivial rank-one submodule. -/
theorem top_eq_zero_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    chernClass δ f E r = ChowCohomology.zeroCap δ f (r : ℤ) :=
  sorry

/-- The Chern class components below the rank agree across a short exact
sequence with a trivial rank-one submodule. -/
theorem component_eq_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (j : ℕ) (hj : j < r) :
    chernClass δ f E j = chernClass δ f F j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
