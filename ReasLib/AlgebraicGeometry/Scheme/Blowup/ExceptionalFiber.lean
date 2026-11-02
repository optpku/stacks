/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RationalSingularity
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

section

/-- The exceptional closed fibre of the blowup is proper over the residue field. -/
instance instIsProperExceptionalFiber
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    IsProper (f.fiberToSpecResidueField (IsLocalRing.closedPoint A)) := by
  change IsProper (pullback.snd f ((Spec (.of A)).fromSpecResidueField
    (IsLocalRing.closedPoint A)))
  infer_instance

/-- The exceptional closed fibre of the blowup is Cohen–Macaulay. -/
instance instCohenMacaulayExceptionalFiber
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    Scheme.CohenMacaulay (f.fiber (IsLocalRing.closedPoint A)) := sorry

/-- The exceptional closed fibre of the blowup is one-dimensional. -/
theorem exceptionalFiber_topologicalKrullDim
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) = 1 := sorry

/-- The exceptional ideal restricted to the closed fibre is relatively very ample. -/
instance instRelativelyVeryAmpleExceptionalTwist
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    RelativelyVeryAmple
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
        (exceptionalIdeal (IsLocalRing.maximalIdeal A) f).negSheaf) := sorry

/-- The degree of the restricted exceptional ideal is at least one. -/
theorem exceptionalTwist_degree_one_le
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    (1 : ℤ) ≤ @Scheme.Modules.curveDegreeOfInvertible _ _ _
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
      (instIsProperExceptionalFiber A f)
      (exceptionalFiber_topologicalKrullDim A f).le
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
        (exceptionalIdeal (IsLocalRing.maximalIdeal A) f).negSheaf) inferInstance := sorry

/-- Degree one for the restricted exceptional ideal implies that `A` is regular local. -/
theorem isRegularLocalRing_of_exceptionalTwist_degree_eq_one
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (h_degree : @Scheme.Modules.curveDegreeOfInvertible _ _ _
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
      (instIsProperExceptionalFiber A f)
      (exceptionalFiber_topologicalKrullDim A f).le
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
        (exceptionalIdeal (IsLocalRing.maximalIdeal A) f).negSheaf) inferInstance = 1) :
    IsRegularLocalRing A := sorry

/-- The first cohomology of every nonnegative tensor power of the restricted exceptional ideal vanishes. -/
theorem exceptionalTwist_firstCohomology_isZero
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) :
    IsZero (Scheme.Hom.cohomology
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
      (Scheme.Modules.tensorPowerInt
        ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (exceptionalIdeal (IsLocalRing.maximalIdeal A) f).negSheaf) (n : ℤ)) 1) := sorry

/-- Degree-zero cohomology of a nonnegative tensor power is the corresponding associated-graded piece. -/
theorem exceptionalTwist_cohomologyZero_iso_piece
    (A : Type u) [CommRing A] [h_domain : IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [h_modification : IsModification f]
    [h_blowup : IsBlowup f
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) :
    IsIsomorphic
      (Scheme.Hom.cohomology
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (Scheme.Modules.tensorPowerInt
          ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
            (exceptionalIdeal (IsLocalRing.maximalIdeal A) f).negSheaf) (n : ℤ)) 0)
      ((ModuleCat.restrictScalars
        ((IsLocalRing.ResidueField.maximalIdealAlgEquiv A).symm.toRingHom.comp
          (Scheme.Spec.residueFieldIso
            (.of A) (IsLocalRing.closedPoint A)).hom.hom)).obj
          (ModuleCat.of (IsLocalRing.ResidueField A)
            (Ideal.AssociatedGraded.piece (IsLocalRing.maximalIdeal A) A n))) := sorry

end

end AlgebraicGeometry.IsBlowup
