/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence

/-!
# Chow groups of algebraic spaces

The Chow group of `k`-cycles on a good algebraic space is the quotient of
`Z_k(X)` by rational equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.rationallyEquivalent_iff_chowMk_eq :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (k : ℤ) (α β : cycleGroup f δ k),
    RationalEquivalence.RationallyEquivalent f δ k α β ↔
      chowMk f δ k α = chowMk f δ k β)

end AlgebraicGeometry.AlgebraicSpace.Hom
