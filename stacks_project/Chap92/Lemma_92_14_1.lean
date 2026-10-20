module

public import ReasLib.RingTheory.CotangentComplex.ConstantCoeff
import StacksCheckRecall

/-!
# Cotangent complex of evaluation at zero on a polynomial ring

This file identifies `L_{B/A}` in `D(B)` with the conormal module `I/I²`
placed in cohomological degree `-1`, for the evaluation map
`MvPolynomial σ R →+* R` sending each variable to `0`.
-/

@[expose] public section

open CategoryTheory
variable (n : ℕ)

/- Lemma 92.14.1. Let `A = MvPolynomial (Fin n) ℤ → B = ℤ` be the ring map sending
each `X i` to `0`. Let `I = Ideal.span (Set.range MvPolynomial.X) ⊂ A`. Then `L_{B/A}`
is quasi-isomorphic to `I.Cotangent` placed in cohomological degree `-1`. Recorded here
as an isomorphism in `D(ℤ)` between `DerivedCategory.Q.obj` of
`RingHom.cotangentComplex MvPolynomial.constantCoeff` and the image of
`ModuleCat.of ℤ I.Cotangent` under `DerivedCategory.singleFunctor` in cohomological
degree `-1`. -/
@[stacks 08SI] #check
  (Algebra.CotangentComplex.constantCoeff_isIsomorphic_single_conormal :
    IsIsomorphic
      (DerivedCategory.Q.obj (RingHom.cotangentComplex
        (MvPolynomial.constantCoeff : MvPolynomial (Fin n) ℤ →+* ℤ)))
      ((DerivedCategory.singleFunctor (ModuleCat.{0} ℤ) (-1 : ℤ)).obj
        (ModuleCat.of ℤ
          ((Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ))).Cotangent))))
