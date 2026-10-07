module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maximal ideals in integral algebras over local rings

The contraction of a maximal ideal along an integral algebra map is the
maximal ideal of the local base.  The named theorem and its canonical
`LiesOver` instance are shared by integral closures and arbitrary integral
algebras alike.

@stack 09EA
-/

universe u v

namespace Ideal

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
variable [Algebra.IsIntegral R S]

/-- A maximal ideal in an integral algebra over a local ring contracts to the
base maximal ideal. -/
@[stacks 09EA "maximal ideals of an integral local algebra lie over the closed point"]
theorem IsMaximal.under_eq_maximalIdeal
    (m : Ideal S) [m.IsMaximal] :
    m.under R = IsLocalRing.maximalIdeal R := sorry

-- Proof strategy: apply `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` to show that
-- `m.under R` is maximal, then identify it with the unique maximal ideal of the local ring `R`
-- using `IsLocalRing.eq_maximalIdeal`, with the equality oriented as stated.

/-- Every maximal ideal in an integral algebra over a local ring lies over
the base maximal ideal. -/
@[stacks 09EA "lying-over maximal ideals in an integral local algebra"]
instance IsMaximal.instLiesOverMaximalIdeal
    (m : Ideal S) [m.IsMaximal] :
    m.LiesOver (IsLocalRing.maximalIdeal R) := sorry

-- Proof strategy: construct `Ideal.LiesOver` from `IsMaximal.under_eq_maximalIdeal m`; the
-- instance contains no additional choice beyond this contraction equality.

end Ideal
