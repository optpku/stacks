module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree

/-!
# Reasonable algebraic spaces

An algebraic space is reasonable when every étale morphism from an affine scheme
has universally bounded fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is reasonable if every étale morphism from an affine scheme has
universally bounded fibres. -/
@[mk_iff]
class IsReasonable {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Affine étale morphisms from schemes into `X` have universally bounded fibres. -/
  affine_etale_universallyBounded {U : Over S} (φ : ofOver U ⟶ X) [IsAffine U.left]
      [Etale φ] : universallyBoundedFibres φ

namespace IsReasonable

/-- A reasonable algebraic space has universally bounded fibres along every affine étale
morphism from a scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReasonable X] {U : Over S}
    (φ : ofOver U ⟶ X) [IsAffine U.left] [Etale φ] : universallyBoundedFibres φ :=
  sorry

/-- An algebraic space is reasonable as soon as every affine étale morphism from a scheme has
universally bounded fibres. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ {U : Over S} (φ : ofOver U ⟶ X) [IsAffine U.left] [Etale φ],
      universallyBoundedFibres φ) : IsReasonable X :=
  sorry

end IsReasonable

/-- A scheme over `S`, viewed as an algebraic space, is reasonable. -/
instance instIsReasonable_ofOver {S : Scheme.{u}} (T : Over S) : IsReasonable (ofOver T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
