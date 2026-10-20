/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Quasi-projectivity of one-dimensional schemes

This file records H-quasi-projectivity for separated finite-type schemes of dimension at most one
over a field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.HQuasiProjective

/-- Every separated finite-type scheme over a field whose topological Krull dimension is at most
one is H-quasi-projective over that field. -/
theorem of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Scheme.Hom.FiniteType f] [IsSeparated f] (hdim : topologicalKrullDim X ≤ 1) :
    HQuasiProjective f := sorry

end AlgebraicGeometry.HQuasiProjective
