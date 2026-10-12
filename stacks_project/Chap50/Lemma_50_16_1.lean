/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter.RelativeForms
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 50.16.1: for a ≥ 0 the map Ω^a_{X/S} → b_* Ω^a_{L/S} is an isomorphism, the map
Ω^a_{Z/S} → p_* Ω^a_{P/S} is an isomorphism, and Rb_* Ω^a_{L/S} → i_* Rp_* Ω^a_{P/S} is an
isomorphism on cohomology sheaves in degree ≥ 1. -/
@[stacks 0FUR]
#check (AlgebraicGeometry.Blowup.CoordinateCenter.formPushforwardComparison_isIso :
  ∀ (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ),
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (AlgebraicGeometry.Blowup.CoordinateCenter.blowupSquare R m n π) a))

#check (AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalFormPushforwardComparison_isIso :
  ∀ (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ),
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalProjectionSquare R m n π) a))

#check (AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalRestrictionCohomologyMap_isIso :
  ∀ (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a q : ℕ) [NeZero q],
    IsIso ((DerivedCategory.homologyFunctor
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))).Modules
      (q : ℤ)).map
      (AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalRestrictionDerivedComparison
        R m n π a)))
