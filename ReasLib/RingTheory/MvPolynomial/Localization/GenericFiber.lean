module

public import ReasLib.RingTheory.MvPolynomial.Localization

@[expose] public section

/-!
# Generic-Fiber Denominators for Multivariate Polynomial Rings

This leaf records how coefficient denominators embed into the denominator
submonoid used for the generic fiber of a multivariate polynomial ring.  The
statements are independent of a finite-variable presentation or a module over
the polynomial ring.

@stack 051T
-/

universe u v

namespace MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A] [IsDomain A]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: powers of a nonzero coefficient, viewed as constant
polynomials, belong to the generic-fiber denominator submonoid. -/
@[stacks 051T "coefficient powers in generic-fiber denominators"]
theorem powers_C_le_genericFiberDenominators {f : A} (hf : f ≠ 0) :
    Submonoid.powers (MvPolynomial.C (σ := σ) f) ≤
      Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A) := sorry

/-- Tag `051T`: adjoining powers of a nonzero coefficient constant does not
enlarge the generic-fiber denominator submonoid. -/
@[stacks 051T "generic-fiber denominator supremum"]
theorem genericFiberDenominators_sup_powers_C {f : A} (hf : f ≠ 0) :
    Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A) ⊔
        Submonoid.powers (MvPolynomial.C (σ := σ) f) =
      Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A) := sorry

end MvPolynomial.Localization
