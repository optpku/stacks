module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CharacteristicZero
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Lifting

/-!
# Degree via characteristic-zero coefficient change

The function-field degree of a projective-line endomorphism can be read after
lifting to a characteristic-zero domain and changing coefficients, including
to `ULift ℂ`. A general finite-type scheme over a finite field need not admit
such a lift.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 64.3.11 (1) -/
@[stacks 03SY] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_complexLift :
    ∀ {k : Type u} [Field k] [Finite k]
      (π : AlgebraicGeometry.ProjectiveSpace.schemeOver k 1 ⟶
        AlgebraicGeometry.ProjectiveSpace.schemeOver k 1)
      [IsIntegral (AlgebraicGeometry.ProjectiveSpace.schemeOver k 1).left]
      [IsDominant π.left],
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : CharZero R)
        (φ : R →+* k) (ψ : R →+* ULift.{u} ℂ)
        (πR : AlgebraicGeometry.ProjectiveSpace.schemeOver R 1 ⟶
          AlgebraicGeometry.ProjectiveSpace.schemeOver R 1)
        (πC : AlgebraicGeometry.ProjectiveSpace.schemeOver (ULift.{u} ℂ) 1 ⟶
          AlgebraicGeometry.ProjectiveSpace.schemeOver (ULift.{u} ℂ) 1)
        (ek : (CategoryTheory.Over.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))).obj
          (AlgebraicGeometry.ProjectiveSpace.schemeOver R 1) ≅
          AlgebraicGeometry.ProjectiveSpace.schemeOver k 1)
        (eC : (CategoryTheory.Over.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ))).obj
          (AlgebraicGeometry.ProjectiveSpace.schemeOver R 1) ≅
          AlgebraicGeometry.ProjectiveSpace.schemeOver (ULift.{u} ℂ) 1)
        (h_complex_integral :
          IsIntegral
            (AlgebraicGeometry.ProjectiveSpace.schemeOver (ULift.{u} ℂ) 1).left)
        (h_complex_dominant : IsDominant πC.left),
        (CategoryTheory.Over.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))).map πR ≫ ek.hom =
            ek.hom ≫ π ∧
        (CategoryTheory.Over.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ))).map πR ≫ eC.hom =
            eC.hom ≫ πC ∧
        -- Local instance justification (proof-local temporary data): Install the existentially supplied integrality proof only to elaborate inducedFunctionFieldDegree.
        letI : IsIntegral
            (AlgebraicGeometry.ProjectiveSpace.schemeOver (ULift.{u} ℂ) 1).left :=
          h_complex_integral
        -- Local instance justification (proof-local temporary data): Install the existentially supplied dominance proof only to elaborate inducedFunctionFieldDegree.
        letI : IsDominant πC.left := h_complex_dominant
        πC.left.inducedFunctionFieldDegree = π.left.inducedFunctionFieldDegree)

/- Remark 64.3.11 (2) -/
@[stacks 03SY] #check
  (AlgebraicGeometry.SchemeOverField.exists_finiteType_not_liftsToCharZero :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k)
      (X : AlgebraicGeometry.SchemeOverField k)
      (_ : AlgebraicGeometry.Scheme.Hom.FiniteType X.hom),
      ¬ AlgebraicGeometry.SchemeOverField.liftsToCharZero X)

#check AlgebraicGeometry.SchemeOverField.liftsToCharZero
#check AlgebraicGeometry.SchemeOverField.liftsToCharZero_iff
#check AlgebraicGeometry.SchemeOverField.liftsToCharZero_projectiveSpace
#check AlgebraicGeometry.ProjectiveSpace.schemeOver_baseChange
#check AlgebraicGeometry.ProjectiveSpace.inducedFunctionFieldDegree_eq_of_charZeroBaseChange
#check AlgebraicGeometry.ProjectiveSpace.inducedFunctionFieldDegree_eq_of_complexBaseChange
