/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.Set.Card
public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.FiniteRange

/-!
# Affine stratifications from weightings

This file relates the affine stratification number of a scheme to the fibre integral of a
positive weighting on a surjective quasi-finite cover by an affine scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/-- If a nonempty separated scheme is the target of a surjective quasi-finite morphism from an
affine scheme, then its affine stratification number is at most the number of values of the fibre
integral of any positive weighting. -/
theorem number_le_fiberIntegralValues
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f] [Hom.QuasiFinite f] [IsAffine X]
    [Y.IsSeparated] [Nonempty Y]
    {w : X → ℤ} (hw : f.IsWeighting w) (h_pos : ∀ x : X, 0 < w x) :
    -- Local instance justification (proof-local temporary data): target compactness is induced by the given continuous surjection.
    letI : CompactSpace Y := Function.Surjective.compactSpace f.continuous f.surjective
    number Y ≤
      (Set.range (f.fiberIntegral (Hom.tendstoCofinite_of_compactSource f) w)).ncard := sorry

end AlgebraicGeometry.Scheme.FiniteAffineStratification
