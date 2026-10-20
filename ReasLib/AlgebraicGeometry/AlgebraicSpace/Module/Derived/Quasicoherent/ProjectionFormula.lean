/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.Source
import Mathlib.Tactic.CrossRefAttribute

/-! # The projection formula for quasi-coherent derived modules -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
variable {S : Scheme.{u}}

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, the canonical
projection-formula mate is an isomorphism on derived modules with quasi-coherent cohomology. -/
@[stacks 08IN]
theorem isIso_projectionFormula {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (leftMate f E.obj K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
