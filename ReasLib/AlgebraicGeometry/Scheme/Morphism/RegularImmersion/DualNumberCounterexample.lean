/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# A dual-number counterexample for regular immersions

The quotient chain `Spec(k[x]/(x)) ⟶ Spec(k[x]/(x)²) ⟶ Spec(k[x])` has regular
composite and second morphism near every source point, although its two factors are not both
regular there.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.DualNumberRegularImmersionCounterexample

variable (k : Type u) [Field k]

/-- The principal ideal `(x)` in the polynomial ring `k[x]`. -/
abbrev ideal : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

/-- The affine line `Spec(k[x])`. -/
abbrev affineLine : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The doubled origin `Spec(k[x]/(x)²)` in the affine line. -/
abbrev doublePoint : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k ⧸ ideal k ^ 2))

/-- The reduced origin `Spec(k[x]/(x))` in the affine line. -/
abbrev closedPoint : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k ⧸ ideal k))

/-- The morphism `Spec(k[x]/(x)) ⟶ Spec(k[x]/(x)²)` induced by the factor map between
the two polynomial quotients. -/
abbrev closedPointEmbedding : closedPoint k ⟶ doublePoint k :=
  Spec.map
    (CommRingCat.ofHom
      (Ideal.Quotient.factor
        (Ideal.pow_le_self two_ne_zero : ideal k ^ 2 ≤ ideal k)))

/-- The canonical quotient morphism `Spec(k[x]/(x)²) ⟶ Spec(k[x])`. -/
abbrev doublePointEmbedding : doublePoint k ⟶ affineLine k :=
  Spec.quotientMap (R := CommRingCat.of (Polynomial k)) (ideal k ^ 2)

/-- The factor-map morphism from the reduced origin to the doubled origin is a closed
immersion. -/
@[instance]
theorem closedPointEmbedding_isClosedImmersion :
    IsClosedImmersion (closedPointEmbedding k) := sorry

/-- The composite from the reduced origin to the affine line is a regular immersion near every
source point. -/
theorem composite_isRegularImmersionNear (z : closedPoint k) :
    IsRegularImmersionNear (closedPointEmbedding k ≫ doublePointEmbedding k) z := sorry

/-- The doubled-origin embedding is a regular immersion near the image of every point of the
reduced origin. -/
theorem doublePointEmbedding_isRegularImmersionNear (z : closedPoint k) :
    IsRegularImmersionNear (doublePointEmbedding k) ((closedPointEmbedding k).base z) := sorry

/-- At every point of the reduced origin, the two consecutive quotient morphisms are not both
regular immersions near their respective source points. -/
theorem not_both_isRegularImmersionNear (z : closedPoint k) :
    ¬ (IsRegularImmersionNear (closedPointEmbedding k) z ∧
      IsRegularImmersionNear (doublePointEmbedding k) ((closedPointEmbedding k).base z)) := sorry

/-- For the quotient chain through the doubled origin, simultaneous regularity of the two
factors is not equivalent to simultaneous regularity of the composite and the second map. -/
theorem regularImmersionNear_factors_not_iff_composite_and_second (z : closedPoint k) :
    ¬ ((IsRegularImmersionNear (closedPointEmbedding k) z ∧
          IsRegularImmersionNear (doublePointEmbedding k) ((closedPointEmbedding k).base z)) ↔
        (IsRegularImmersionNear (closedPointEmbedding k ≫ doublePointEmbedding k) z ∧
          IsRegularImmersionNear (doublePointEmbedding k)
            ((closedPointEmbedding k).base z))) := sorry

end AlgebraicGeometry.DualNumberRegularImmersionCounterexample
