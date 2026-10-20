/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Retract
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-!
# Retract extensions of perfect complexes from open subspaces

On a quasi-compact quasi-separated algebraic space, a perfect object of `D(𝒪_W)` on a
quasi-compact open subspace is a direct summand of the restriction of a globally perfect
object of `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A perfect object of `D(𝒪_W)` on a quasi-compact open subspace of a quasi-compact
quasi-separated algebraic space is a direct summand of the restriction of a perfect
object of `D(𝒪_X)`. -/
theorem exists_retract_extension_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (W : OpenSubspace X)
    [IsQuasiCompact W.X] (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P) :
    ∃ R : ModuleDerived X,
      ModuleDerived.IsPerfect R ∧
        Nonempty (Retract P ((ModuleDerived.pullback W.ι).obj R)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
