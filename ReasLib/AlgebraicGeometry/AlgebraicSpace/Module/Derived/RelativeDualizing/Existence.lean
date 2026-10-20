/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

variable {S : Scheme.{u}}

/-- A proper, flat, finitely presented morphism of algebraic spaces admits a relative
dualizing complex. -/
theorem nonempty {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] :
    Nonempty (RelativeDualizingComplex f) := sorry

/-- Existence of a relative dualizing complex is equivalent to existence of a
`Y`-perfect pair `(ω, τ)` satisfying the affine cartesian base-change condition. -/
theorem nonempty_iff {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] :
    Nonempty (RelativeDualizingComplex f) ↔
      ∃ (ω : ModuleDerived X)
        (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y),
        ModuleDerived.IsPerfectRelativeTo f ω ∧ affineBaseChangeCondition f ω τ := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
