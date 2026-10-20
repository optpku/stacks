module

public import ReasLib.RingTheory.MvPolynomial.OriginIntersection
import StacksCheckRecall

@[expose] public section

universe u
/- Exercise 111.9.4: for a field `k`, the localized intersection of the two
explicit plane curves at the origin has module length `9`. -/
@[stacks 02DL] #check (MvPolynomial.originCurves_length :
  ∀ (k : Type u) [Field k],
    Module.length (MvPolynomial.originLocalRing k)
        (MvPolynomial.originLocalRing k ⧸ Ideal.span
          {algebraMap (MvPolynomial (Fin 2) k) (MvPolynomial.originLocalRing k)
              (MvPolynomial.originCurveF k),
            algebraMap (MvPolynomial (Fin 2) k) (MvPolynomial.originLocalRing k)
              (MvPolynomial.originCurveG k)}) =
      (9 : ℕ∞))
