/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearEquivalence
public import stacks_project.Chap111.Exercise_111_46_4_PointSum

/-!
# Linear equivalence of a difference to an effective Cartier divisor

The unbundled predicate that `D - E` is linearly equivalent to some effective
Cartier divisor, together with the associated-sheaf form and the point-sum
difference module `𝒪(∑ x i - ∑ y j)`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The difference `D - E` of effective Cartier divisors is linearly equivalent to an
effective Cartier divisor when `D` is linearly equivalent to `E + F` for some
effective Cartier divisor `F`. -/
def differenceLinearlyEquivalentToEffective {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι]
    [hE : IsEffectiveCartierDivisor E.subschemeι] : Prop :=
  ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
    @linearlyEquivalent X D (effectiveCartierDivisorSum E F) hD
      (@instIsEffectiveCartierDivisorSum X E F hE hF)

/-- Unfold linear equivalence of a difference to an effective divisor as linear
equivalence of `D` with a sum `E + F`. -/
theorem differenceLinearlyEquivalentToEffective_iff {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι]
    [hE : IsEffectiveCartierDivisor E.subschemeι] :
    differenceLinearlyEquivalentToEffective D E ↔
      ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
        @linearlyEquivalent X D (effectiveCartierDivisorSum E F) hD
          (@instIsEffectiveCartierDivisorSum X E F hE hF) :=
  sorry

/-- The difference `D - E` is linearly equivalent to an effective Cartier divisor if
and only if `𝒪(D - E)` is isomorphic to the associated sheaf of some effective
Cartier divisor. -/
theorem differenceLinearlyEquivalentToEffective_iff_associatedSheaf {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    differenceLinearlyEquivalentToEffective D E ↔
      ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
        Nonempty (D.differenceSheaf E ≅ @associatedSheaf X F hF) :=
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Curve

/-- The invertible module `𝒪(∑ x i - ∑ y j)` associated to a pair of point-sum
divisors. -/
noncomputable abbrev pointSumDifferenceSheaf
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    {r s : ℕ} (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left)
    (y : Fin s → X.left) (hy : ∀ j, y j ∈ closedPoints X.left) :
    X.left.Modules :=
  (pointSumDivisor X x hx).differenceSheaf (pointSumDivisor X y hy)

/-- Unfold the point-sum difference sheaf as the difference sheaf of the two
point-sum divisors. -/
theorem pointSumDifferenceSheaf_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    {r s : ℕ} (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left)
    (y : Fin s → X.left) (hy : ∀ j, y j ∈ closedPoints X.left) :
    pointSumDifferenceSheaf X x hx y hy =
      (pointSumDivisor X x hx).differenceSheaf (pointSumDivisor X y hy) :=
  sorry

end AlgebraicGeometry.Curve
