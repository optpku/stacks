module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Descent
import StacksCheckRecall

/-!
# Spreading out a relative global complete intersection

@stack 00SU
-/

@[expose] public section

universe u

namespace Algebra

variable {R : Type u} [CommRing R]
variable {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
variable (h : IsRelativeGlobalCompleteIntersection R
  (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))

@[stacks 00SU]
#check (h.exists_finiteType_model :
  ∃ (R₀ : Subalgebra ℤ R) (f₀ : Fin c → MvPolynomial (Fin n) R₀),
    Algebra.FiniteType ℤ R₀ ∧
      (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
        IsRelativeGlobalCompleteIntersection R₀
          (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)))

end Algebra
