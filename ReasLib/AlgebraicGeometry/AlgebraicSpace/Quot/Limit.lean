/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Preservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Directed affine limits of finitely presented quotients
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces and a quasi-coherent
finitely presented module, the functor of finitely presented quotients flat over the test scheme
preserves directed inverse limits of affine schemes over the base. -/
@[stacks 082Q]
theorem fpFunctor_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    SchemeOver.PreservesDirectedAffineLimits B (fpFunctor f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
