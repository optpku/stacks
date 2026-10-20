module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.PolynomialSite
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Cotangent complexes of polynomial algebras

For a polynomial algebra, the cotangent complex is concentrated in degree zero,
where it agrees with the module of Kähler differentials.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

namespace Algebra.CotangentComplex

section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsPolynomial A B]

/-- The cotangent complex of a polynomial algebra is isomorphic in its derived category to
the module of relative Kähler differentials concentrated in degree zero. -/
theorem isIsomorphic_single_kaehler :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (ModuleCat.of B Ω[B⁄A])) :=
  sorry

/-- The homology of the cotangent complex of a polynomial algebra vanishes in every nonzero
cohomological degree. -/
theorem homology_isZero_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

end

end Algebra.CotangentComplex
