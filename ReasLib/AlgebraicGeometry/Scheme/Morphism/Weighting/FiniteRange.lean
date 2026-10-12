/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Maximum

/-!
# Finite ranges of fibre integrals

This file records finiteness of the range of the fibre integral of a nonnegative weighting on a
locally finite-type, locally quasi-finite morphism with compact source.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre integral of a nonnegative weighting on a locally finite-type, locally quasi-finite
morphism with compact source takes only finitely many values. -/
theorem IsWeighting.fiberIntegral_range_finite
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] {w : X → ℤ} (hw : f.IsWeighting w) (h_nonneg : ∀ x : X, 0 ≤ w x) :
    (Set.range (f.fiberIntegral (tendstoCofinite_of_compactSource f) w)).Finite := sorry

end AlgebraicGeometry.Scheme.Hom
