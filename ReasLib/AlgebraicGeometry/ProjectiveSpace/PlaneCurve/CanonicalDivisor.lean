module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.GenericStalk
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk

/-!
# The divisor of the canonical rational differential on a normalized plane curve

The standard coordinates determine a rational differential on the normalization.
Its generic stalk extends to a global meromorphic differential, whose intrinsic
orders of vanishing define a Weil divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- Relative differentials of the abstract curve are invertible. -/
instance instInvertible_differentials_abstractCurve {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom]) := sorry

/-- Transport of `canonicalForm F` to `Ω[k(C)⁄k]` along a function-field identification. -/
def canonicalFormAlongIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    Ω[SchemeOverField.functionFieldCommAlg (abstractCurve d F hF) ⁄ k] :=
  @KaehlerDifferential.map k k _ _ _
    (fractionField F) (SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
    _ _ _ e.toAlgHom.toAlgebra _ _ (IsScalarTower.of_algHom e.toAlgHom) _ _
    (canonicalForm F)

/-- `canonicalFormAlongIdent` is Kähler transport of `canonicalForm F` along `e`. -/
theorem canonicalFormAlongIdent_eq_map {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    canonicalFormAlongIdent d F hF e =
      @KaehlerDifferential.map k k _ _ _
        (fractionField F) (SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
        _ _ _ e.toAlgHom.toAlgebra _ _ (IsScalarTower.of_algHom e.toAlgHom) _ _
        (canonicalForm F) := rfl

/-- The inverse-image structure sheaf map of the structure morphism of `C`. -/
abbrev abstractCurveStructureSheafHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm
    (abstractCurve d F hF).hom.toShHom

/-- `abstractCurveStructureSheafHom` is the inverse-image structure map of `C ⟶ Spec k`. -/
theorem abstractCurveStructureSheafHom_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    abstractCurveStructureSheafHom d F hF =
      RingedSpace.Hom.inverseImageStructureSheafHomComm
        (abstractCurve d F hF).hom.toShHom := rfl

/-- The image of `canonicalForm F` in the Kähler module of the generic stalk map of `C ⟶ Spec k`. -/
def canonicalFormStalkTarget {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    TopCat.Sheaf.RelativeDifferentials.Stalk.target
      (abstractCurveStructureSheafHom d F hF)
      (genericPoint (abstractCurve d F hF).left) :=
  open Classical in
    if identApply d F hF e (pderivYFrac F) = 0 then
      -(identApply d F hF e (pderivXFrac F))⁻¹ •
        CommRingCat.KaehlerDifferential.d (identApply d F hF e (yFrac F))
    else
      (identApply d F hF e (pderivYFrac F))⁻¹ •
        CommRingCat.KaehlerDifferential.d (identApply d F hF e (xFrac F))

/-- On the locus `e f_y ≠ 0`, the stalk-target form is `d(e x) / e f_y`. -/
theorem canonicalFormStalkTarget_eq_smul_dX {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF)
    (hfy : identApply d F hF e (pderivYFrac F) ≠ 0) :
    canonicalFormStalkTarget d F hF e =
      (identApply d F hF e (pderivYFrac F))⁻¹ •
        CommRingCat.KaehlerDifferential.d (identApply d F hF e (xFrac F)) := by
  simp only [canonicalFormStalkTarget, if_neg hfy]

/-- On the locus `e f_x ≠ 0`, the stalk-target form is `- d(e y) / e f_x`. -/
theorem canonicalFormStalkTarget_eq_neg_smul_dY {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF)
    (hfx : identApply d F hF e (pderivXFrac F) ≠ 0) :
    canonicalFormStalkTarget d F hF e =
      -(identApply d F hF e (pderivXFrac F))⁻¹ •
        CommRingCat.KaehlerDifferential.d (identApply d F hF e (yFrac F)) := sorry

/-- The canonical image of `canonicalForm F` in the generic stalk of `Ω[C/k]`. -/
def canonicalFormGenericStalk {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    RingedSpace.stalkModuleCat (Ω[(abstractCurve d F hF).hom.toShHom])
      (genericPoint (abstractCurve d F hF).left) :=
  TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv
    (abstractCurveStructureSheafHom d F hF)
    (genericPoint (abstractCurve d F hF).left)
    (canonicalFormStalkTarget d F hF e)

/-- `canonicalFormGenericStalk` is the inverse stalk comparison applied to the stalk-target form. -/
theorem canonicalFormGenericStalk_eq_comparisonInv {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    canonicalFormGenericStalk d F hF e =
      TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv
        (abstractCurveStructureSheafHom d F hF)
        (genericPoint (abstractCurve d F hF).left)
        (canonicalFormStalkTarget d F hF e) := rfl

/-- A Weil divisor on `C` is a divisor of zeros and poles of `canonicalForm F` when it is
the Weil divisor of a nonzero meromorphic section of `Ω[C ⟶ Spec k]` whose generic germ
equals the canonical stalk image of `canonicalForm F` along a standard `X 0`-chart
identification. -/
def IsZerosPolesDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])]
    (W : WeilDivisor (abstractCurve d F hF).left) : Prop :=
  ∃ (e : fractionFieldAbstractCurveIdent d F hF)
    (s : (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSections
      (Ω[(abstractCurve d F hF).hom.toShHom]))
    (hs : s ≠ 0),
    IsStandardChartIdent d F hF e ∧
      SheafOfModules.sectionGermOfCommRing s
          (genericPoint (abstractCurve d F hF).left) =
        (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSectionStalkMap
          (Ω[(abstractCurve d F hF).hom.toShHom])
          (genericPoint (abstractCurve d F hF).left)
          (canonicalFormGenericStalk d F hF e) ∧
        W = Scheme.nonzeroMeromorphicSectionWeilDivisor (abstractCurve d F hF).left
          (Ω[(abstractCurve d F hF).hom.toShHom]) s hs

/-- Unfold `IsZerosPolesDivisor` into the meromorphic-section Weil divisor associated
to the standard-chart image of `canonicalForm F`. -/
theorem isZerosPolesDivisor_iff {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])]
    (W : WeilDivisor (abstractCurve d F hF).left) :
    IsZerosPolesDivisor d F hF W ↔
      ∃ (e : fractionFieldAbstractCurveIdent d F hF)
        (s : (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSections
          (Ω[(abstractCurve d F hF).hom.toShHom]))
        (hs : s ≠ 0),
        IsStandardChartIdent d F hF e ∧
          SheafOfModules.sectionGermOfCommRing s
              (genericPoint (abstractCurve d F hF).left) =
            (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSectionStalkMap
              (Ω[(abstractCurve d F hF).hom.toShHom])
              (genericPoint (abstractCurve d F hF).left)
              (canonicalFormGenericStalk d F hF e) ∧
            W = Scheme.nonzeroMeromorphicSectionWeilDivisor (abstractCurve d F hF).left
              (Ω[(abstractCurve d F hF).hom.toShHom]) s hs := Iff.rfl

/-- The canonical rational differential gives a nonzero vector in the generic
stalk of the normalized plane curve's differential sheaf. -/
theorem canonicalFormGenericStalk_ne_zero {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    canonicalFormGenericStalk d F hF e ≠ 0 := sorry

/-- The canonical meromorphic differential extends the canonical generic vector
through the standard coordinate identification of function fields. -/
def canonicalMeromorphicSection {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSections
      (Ω[(abstractCurve d F hF).hom.toShHom]) :=
  Scheme.meromorphicSectionOfGenericStalk (abstractCurve d F hF).left
    (Ω[(abstractCurve d F hF).hom.toShHom])
    (canonicalFormGenericStalk d F hF (standardChartIdent d F hF))

/-- The generic germ of the canonical meromorphic differential is the prescribed
canonical vector under meromorphic scalar extension. -/
theorem canonicalMeromorphicSection_germ {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    SheafOfModules.sectionGermOfCommRing (canonicalMeromorphicSection d F hF)
        (genericPoint (abstractCurve d F hF).left) =
      (abstractCurve d F hF).left.toLocallyRingedSpace.meromorphicSectionStalkMap
        (Ω[(abstractCurve d F hF).hom.toShHom])
        (genericPoint (abstractCurve d F hF).left)
        (canonicalFormGenericStalk d F hF (standardChartIdent d F hF)) :=
  Scheme.meromorphicSectionOfGenericStalk_germ (abstractCurve d F hF).left
    (Ω[(abstractCurve d F hF).hom.toShHom]) _

/-- The canonical meromorphic differential on the normalized plane curve is nonzero. -/
theorem canonicalMeromorphicSection_ne_zero {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    canonicalMeromorphicSection d F hF ≠ 0 :=
  Scheme.meromorphicSectionOfGenericStalk_ne_zero (abstractCurve d F hF).left
    (Ω[(abstractCurve d F hF).hom.toShHom]) _
    (canonicalFormGenericStalk_ne_zero d F hF (standardChartIdent d F hF))

/-- The canonical divisor is the Weil divisor of the canonical nonzero
meromorphic differential. -/
def canonicalDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    WeilDivisor (abstractCurve d F hF).left :=
  Scheme.nonzeroMeromorphicSectionWeilDivisor (abstractCurve d F hF).left
    (Ω[(abstractCurve d F hF).hom.toShHom]) (canonicalMeromorphicSection d F hF)
    (canonicalMeromorphicSection_ne_zero d F hF)

/-- The canonical divisor is the divisor of zeros and poles of the canonical
rational differential under the standard coordinate identification. -/
theorem canonicalDivisor_spec {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    IsZerosPolesDivisor d F hF (canonicalDivisor d F hF) := sorry

/-- A divisor of zeros and poles of the canonical rational differential equals
the canonical divisor. -/
theorem eq_canonicalDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])]
    {W : WeilDivisor (abstractCurve d F hF).left}
    (hW : IsZerosPolesDivisor d F hF W) :
    W = canonicalDivisor d F hF := sorry

/-- The canonical rational differential has a unique divisor of zeros and poles. -/
theorem existsUnique_zerosPolesDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    ∃! W, IsZerosPolesDivisor d F hF W :=
  ⟨canonicalDivisor d F hF, canonicalDivisor_spec d F hF,
    fun _ hW => eq_canonicalDivisor d F hF hW⟩

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
