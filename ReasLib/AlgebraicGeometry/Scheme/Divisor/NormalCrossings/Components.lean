/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Components of strict normal crossings divisors

This module characterizes strict normal crossings divisors through their reduced components and
the regularity and codimension of finite nonempty component intersections.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

namespace IsStrictNormalCrossingsDivisor

/-- A strict normal crossings divisor is reduced. -/
instance instIsReducedSubscheme (D : X.IdealSheafData)
    [IsStrictNormalCrossingsDivisor D] : IsReduced D.subscheme := sorry

/-- Every reduced irreducible component of a strict normal crossings divisor is an effective
Cartier divisor in the ambient scheme. -/
instance instIsEffectiveCartierDivisorComponent (D : X.IdealSheafData)
    [IsStrictNormalCrossingsDivisor D] (i : irreducibleComponents D.subscheme) :
    IsEffectiveCartierDivisor (D.reducedComponent i).subschemeι := sorry

/-- Every finite nonempty scheme-theoretic intersection of reduced irreducible components of a
strict normal crossings divisor is regular. -/
theorem componentIntersection_regular (D : X.IdealSheafData)
    [IsStrictNormalCrossingsDivisor D] (J : Finset (irreducibleComponents D.subscheme))
    (hJ : J.Nonempty) : Scheme.Regular (D.componentIntersection J).subscheme := sorry

/-- Every irreducible component of an intersection indexed by a finite nonempty set `J` has
codimension `J.card` in the ambient scheme. -/
theorem componentIntersection_codimension (D : X.IdealSheafData)
    [IsStrictNormalCrossingsDivisor D] (J : Finset (irreducibleComponents D.subscheme))
    (hJ : J.Nonempty) (ξ : (D.componentIntersection J).subscheme)
    (hξ : ξ ∈ genericPoints (D.componentIntersection J).subscheme) :
    ringKrullDim (X.presheaf.stalk ((D.componentIntersection J).subschemeι.base ξ)) =
      J.card := sorry

end IsStrictNormalCrossingsDivisor

/-- An effective Cartier divisor is a strict normal crossings divisor if it is reduced, its
reduced irreducible components are effective Cartier divisors, and every finite nonempty
component intersection is regular of the expected ambient codimension. -/
theorem isStrictNormalCrossingsDivisor_of_components (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (h_reduced : IsReduced D.subscheme)
    (h_cartier : ∀ i : irreducibleComponents D.subscheme,
      IsEffectiveCartierDivisor (D.reducedComponent i).subschemeι)
    (h_regular : ∀ (J : Finset (irreducibleComponents D.subscheme)), J.Nonempty →
      Scheme.Regular (D.componentIntersection J).subscheme)
    (h_codimension : ∀ (J : Finset (irreducibleComponents D.subscheme)), J.Nonempty →
      ∀ ξ : (D.componentIntersection J).subscheme,
        ξ ∈ genericPoints (D.componentIntersection J).subscheme →
          ringKrullDim
              (X.presheaf.stalk ((D.componentIntersection J).subschemeι.base ξ)) = J.card) :
    IsStrictNormalCrossingsDivisor D := sorry

/-- An effective Cartier divisor has strict normal crossings exactly when it is reduced, its
reduced irreducible components are effective Cartier divisors, and every finite nonempty
component intersection is regular of the expected ambient codimension. -/
theorem isStrictNormalCrossingsDivisor_iff_components (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    IsStrictNormalCrossingsDivisor D ↔
      IsReduced D.subscheme ∧
        (∀ i : irreducibleComponents D.subscheme,
          IsEffectiveCartierDivisor (D.reducedComponent i).subschemeι) ∧
          ∀ J : Finset (irreducibleComponents D.subscheme), J.Nonempty →
            Scheme.Regular (D.componentIntersection J).subscheme ∧
              ∀ ξ : (D.componentIntersection J).subscheme,
                ξ ∈ genericPoints (D.componentIntersection J).subscheme →
                  ringKrullDim
                      (X.presheaf.stalk ((D.componentIntersection J).subschemeι.base ξ)) =
                    J.card := sorry

end AlgebraicGeometry
