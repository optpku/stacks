/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- The degree-`d` Hilbert functor of a finitely presented scheme preserves directed
inverse limits of affine schemes over the base. -/
theorem functor_preservesDirectedAffineLimits {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [Scheme.Hom.FinitePresentation X.hom] :
    Scheme.Over.PreservesDirectedAffineLimits S (functor X d) := sorry

end AlgebraicGeometry.Hilbert
