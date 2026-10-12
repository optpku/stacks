/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic

/-!
# Finite-type models of relative global complete intersections

This leaf is the fixed-`ℤ` subalgebra bridge from general descent results to
displayed relative global complete intersection quotients. It retains the
relations whose coefficients must descend.

@stack 00SU
-/

@[expose] public section

universe u

namespace Algebra.IsRelativeGlobalCompleteIntersection

variable {R : Type u} [CommRing R]

/-- A quotient by finitely many displayed polynomial relations that is a
relative global complete intersection descends, together with its relations,
to a finite-type `ℤ`-subalgebra of the coefficient ring. -/
@[stacks 00SU]
theorem exists_finiteType_model
    {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
    (h : Algebra.IsRelativeGlobalCompleteIntersection R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ (R₀ : Subalgebra ℤ R) (f₀ : Fin c → MvPolynomial (Fin n) R₀),
      Algebra.FiniteType ℤ R₀ ∧
        (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
          Algebra.IsRelativeGlobalCompleteIntersection R₀
            (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := sorry

end Algebra.IsRelativeGlobalCompleteIntersection
