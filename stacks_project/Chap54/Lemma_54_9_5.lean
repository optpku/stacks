/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 54.9.5 (1): the exceptional closed fibre of the blowup is proper over
the residue field of `A`. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.instIsProperExceptionalFiber :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      IsProper (f.fiberToSpecResidueField (IsLocalRing.closedPoint A)))

/- Lemma 54.9.5 (2): the exceptional closed fibre of the blowup is
Cohen–Macaulay. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.instCohenMacaulayExceptionalFiber :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      Scheme.CohenMacaulay (f.fiber (IsLocalRing.closedPoint A)))

/- Lemma 54.9.5 (3): the exceptional closed fibre of the blowup is
one-dimensional. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.exceptionalFiber_topologicalKrullDim :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) = 1)

/- Lemma 54.9.5 (4): the restriction of the exceptional ideal to the closed
fibre is very ample over the residue field. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.instRelativelyVeryAmpleExceptionalTwist :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      RelativelyVeryAmple
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (AlgebraicGeometry.IsBlowup.exceptionalIdeal
            (IsLocalRing.maximalIdeal A) f).negSheaf))

/- Lemma 54.9.5 (5): the degree of the restricted exceptional ideal is at
least one. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.exceptionalTwist_degree_one_le :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      (1 : ℤ) ≤ @Scheme.Modules.curveDegreeOfInvertible _ _ _
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (AlgebraicGeometry.IsBlowup.instIsProperExceptionalFiber A f)
        (AlgebraicGeometry.IsBlowup.exceptionalFiber_topologicalKrullDim A f).le
        ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (AlgebraicGeometry.IsBlowup.exceptionalIdeal
            (IsLocalRing.maximalIdeal A) f).negSheaf) inferInstance)

/- Lemma 54.9.5 (6): if the restricted exceptional ideal has degree one,
then `A` is a regular local ring. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.isRegularLocalRing_of_exceptionalTwist_degree_eq_one :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (h_degree : @Scheme.Modules.curveDegreeOfInvertible _ _ _
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (AlgebraicGeometry.IsBlowup.instIsProperExceptionalFiber A f)
        (AlgebraicGeometry.IsBlowup.exceptionalFiber_topologicalKrullDim A f).le
        ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (AlgebraicGeometry.IsBlowup.exceptionalIdeal
            (IsLocalRing.maximalIdeal A) f).negSheaf) inferInstance = 1),
      IsRegularLocalRing A)

/- Lemma 54.9.5 (7): the first cohomology of every nonnegative tensor power
of the restricted exceptional ideal vanishes. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.exceptionalTwist_firstCohomology_isZero :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (n : ℕ),
      IsZero (Scheme.Hom.cohomology
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (Scheme.Modules.tensorPowerInt
          ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
            (AlgebraicGeometry.IsBlowup.exceptionalIdeal
              (IsLocalRing.maximalIdeal A) f).negSheaf) (n : ℤ)) 1))

/- Lemma 54.9.5 (8): degree-zero cohomology of a nonnegative tensor power of
the restricted exceptional ideal is the corresponding maximal-ideal associated-graded piece. -/
@[stacks 0B63]
#check
  (AlgebraicGeometry.IsBlowup.exceptionalTwist_cohomologyZero_iso_piece :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (n : ℕ),
      IsIsomorphic
        (Scheme.Hom.cohomology
          (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
          (Scheme.Modules.tensorPowerInt
            ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
              (AlgebraicGeometry.IsBlowup.exceptionalIdeal
                (IsLocalRing.maximalIdeal A) f).negSheaf) (n : ℤ)) 0)
        ((ModuleCat.restrictScalars
          ((IsLocalRing.ResidueField.maximalIdealAlgEquiv A).symm.toRingHom.comp
            (Scheme.Spec.residueFieldIso
              (.of A) (IsLocalRing.closedPoint A)).hom.hom)).obj
            (ModuleCat.of (IsLocalRing.ResidueField A)
              (Ideal.AssociatedGraded.piece (IsLocalRing.maximalIdeal A) A n))))
