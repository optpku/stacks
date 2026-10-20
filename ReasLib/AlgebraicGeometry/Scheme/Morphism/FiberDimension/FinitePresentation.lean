/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target

/-!
# Fibre-dimension loci for finitely presented morphisms

This leaf records retrocompactness of upper-bound loci for locally finitely presented morphisms
and local constructibility of exact fibre-dimension loci for finite-presentation morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finitely presented morphism, the locus where the local fibre dimension is at
most `n` is retrocompact. -/
theorem isRetrocompact_fiberDimensionLELocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (n : ℕ) :
    IsRetrocompact (f.fiberDimensionLELocus n) := sorry

namespace FinitePresentation

/-- For a finite-presentation morphism, every level set of the target-indexed fibre-dimension
function is locally constructible. -/
@[stacks 05F9]
theorem fiberDimension_levelSet_isLocallyConstructible {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f] (n : WithBot ℕ∞) :
    Topology.IsLocallyConstructible {y : Y | f.fiberDimension y = n} := sorry

end FinitePresentation

end AlgebraicGeometry.Scheme.Hom
