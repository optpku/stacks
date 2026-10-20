module

public import ReasLib.RingTheory.CohenMacaulay.Regular
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import ReasLib.RingTheory.Polynomial.LocalizationAtX
public import ReasLib.RingTheory.MvPolynomial.Cusp
public import ReasLib.RingTheory.MvPolynomial.LineWithEmbeddedPoint
import StacksCheckRecall

/-!
# Exercise 111.13.1

The six local-ring questions have answers yes, yes, yes, yes, yes, and no.
-/

universe u

section Integers

variable (p : ℕ) [Fact p.Prime]

/- Exercise 111.13.1 (1): the prime-local integers are Cohen--Macaulay (yes). -/
@[stacks 0CT4] #check (Module.CohenMacaulay.self_of_isRegularLocalRing :
  Module.CohenMacaulay (Int.LocalizationAtPrime p) (Int.LocalizationAtPrime p))

/- Exercise 111.13.1 (2): the prime-local integers are regular local (yes). -/
@[stacks 0CT4] #check (Int.localizationAtPrime_isRegularLocalRing p :
  IsRegularLocalRing (Int.LocalizationAtPrime p))

end Integers

section Fields

variable (k : Type u) [Field k]

/- Exercise 111.13.1 (3): localization of `k[x]` at `(x)` is Cohen--Macaulay (yes). -/
@[stacks 0CT4] #check (Module.CohenMacaulay.self_of_isRegularLocalRing :
  Module.CohenMacaulay (Localization.AtPrime (Ideal.span {(Polynomial.X : Polynomial k)}))
    (Localization.AtPrime (Ideal.span {(Polynomial.X : Polynomial k)})))

/- Exercise 111.13.1 (4): localization of `k[x]` at `(x)` is regular local (yes). -/
@[stacks 0CT4] #check (Polynomial.localizationAtX_isRegularLocalRing k :
  IsRegularLocalRing (Localization.AtPrime (Ideal.span {(Polynomial.X : Polynomial k)})))

/- Exercise 111.13.1 (5): `(k[x,y]/(y²-x³))` localized at `(x,y)` is Cohen--Macaulay
(yes), equivalently the quotient of `k[x,y]_(x,y)` by the extended cusp relation. -/
@[stacks 0CT4] #check (MvPolynomial.Cusp.localRing_cohenMacaulay k :
  Module.CohenMacaulay (MvPolynomial.Cusp.LocalRing k) (MvPolynomial.Cusp.LocalRing k))

/- Exercise 111.13.1 (6): `(k[x,y]/(y²,xy))` localized at `(x,y)` is not Cohen--Macaulay
(no), equivalently the quotient of `k[x,y]_(x,y)` by the extended relation ideal.
In the reused presentation, source `x` is `MvPolynomial.LineWithEmbeddedPoint.coordY`
and source `y` is `MvPolynomial.LineWithEmbeddedPoint.coordX`. -/
@[stacks 0CT4] #check (MvPolynomial.LineWithEmbeddedPoint.localRing_not_cohenMacaulay k :
  ¬ Module.CohenMacaulay (MvPolynomial.LineWithEmbeddedPoint.LocalRing k)
    (MvPolynomial.LineWithEmbeddedPoint.LocalRing k))

end Fields
