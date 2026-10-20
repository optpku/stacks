module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.InverseLimit
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.Polynomial
import StacksCheckRecall

/-!
# Lemma 88.2.1

Inverse limits reconstruct finite-type adic algebra systems. Finite-variable polynomial
completions are topologically finite type, and every topologically finite type algebra
is a quotient of one of these completions.
-/

@[expose] public section

open CategoryTheory

universe u

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

/- Lemma 88.2.1 (1). The inverse-limit functor is a quasi-inverse of the adic
quotient-system functor for a finitely generated ideal. -/
@[stacks 0AJP] #check (AdicAlgebraSystem.limitFunctorQuasiInverse I hI :
  (CommAlgCat.TopologicallyFiniteType.toAdicSystem I).QuasiInverse)

#check (AdicAlgebraSystem.limitFunctorQuasiInverse_inverse I hI :
  (AdicAlgebraSystem.limitFunctorQuasiInverse I hI).inverse =
    AdicAlgebraSystem.limitFunctor I hI)

/- Lemma 88.2.1 (2). The adic completion of a finite-variable polynomial ring
is a topologically finite type algebra. -/
@[stacks 0AJP] #check (CommAlgCat.TopologicallyFiniteType.mvPolynomialCompletion I hI :
  ℕ → CommAlgCat.TopologicallyFiniteType.{u} A I)

#check (CommAlgCat.TopologicallyFiniteType.mvPolynomialCompletion_obj I hI :
  ∀ r : ℕ, (CommAlgCat.TopologicallyFiniteType.mvPolynomialCompletion I hI r).obj =
    CommAlgCat.of A (IAdicRestrictedPowerSeries (Fin r) I))

/- Lemma 88.2.1 (3). Every topologically finite type algebra is isomorphic to
an ideal quotient of a finite-variable polynomial completion. -/
@[stacks 0AJP] #check (Algebra.TopologicallyFiniteType.exists_isQuotient_polynomialCompletion I hI :
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B],
    ∃ (r : ℕ) (J : Ideal (IAdicRestrictedPowerSeries (Fin r) I)),
      Nonempty (B ≃ₐ[A] IAdicRestrictedPowerSeries (Fin r) I ⧸ J))
