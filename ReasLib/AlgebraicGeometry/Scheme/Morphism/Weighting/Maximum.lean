/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.FieldValuedPoint

/-!
# Maxima of fibre integrals

This file records boundedness and maximum attainment for fibre integrals of weightings on
locally finite-type, locally quasi-finite morphisms with compact source.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre integral of a weighting on a locally finite-type, locally quasi-finite morphism
with compact source is bounded above. -/
theorem IsWeighting.fiberIntegral_bddAbove
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] {w : X → ℤ} (hw : f.IsWeighting w) :
    BddAbove (Set.range (f.fiberIntegral (tendstoCofinite_of_compactSource f) w)) := sorry

/-- The fibre integral of a weighting on a locally finite-type, locally quasi-finite morphism
with compact source and inhabited target attains its maximum. -/
theorem IsWeighting.exists_isGreatest_fiberIntegral
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] [Nonempty Y] {w : X → ℤ} (hw : f.IsWeighting w) :
    ∃ d : ℤ, IsGreatest
      (Set.range (f.fiberIntegral (tendstoCofinite_of_compactSource f) w)) d := sorry

end AlgebraicGeometry.Scheme.Hom
