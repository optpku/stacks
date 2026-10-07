module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import stacks_project.Chap72.Lemma_72_6_3

/-!
# Order of vanishing of rational units along prime divisors

On a locally Noetherian integral algebraic space, the order of a rational unit
along a prime divisor is the length difference of principal quotients of the
henselian local ring at the generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

namespace PrimeDivisor

/-- The order of vanishing of a rational unit along a prime divisor, as the
length difference of a nonzerodivisor presentation of its image under
`functionFieldToHenselianFraction`. -/
def ord (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  let ab :=
    IsLocalization.sec (nonZeroDivisors A)
      (functionFieldToHenselianFraction Z (f : RationalFunction X))
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

/-- If `functionFieldToHenselianFraction` sends `f` to `IsLocalization.mk' a ⟨b, hb⟩`
with `a` and `b` nonzerodivisors, then the order is the corresponding length
difference in `O_{X, ξ}^h`. -/
theorem ord_spec (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : functionFieldToHenselianFraction Z (f : RationalFunction X) =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
        a ⟨b, hb⟩) :
    ord Z f =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ) :=
  sorry

/-- The order is the difference of principal-quotient lengths in `O_{X, ξ}^h`. -/
theorem ord_eq_length (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : functionFieldToHenselianFraction Z (f : RationalFunction X) =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
        a ⟨b, hb⟩) :
    ord Z f =
      ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ) :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
