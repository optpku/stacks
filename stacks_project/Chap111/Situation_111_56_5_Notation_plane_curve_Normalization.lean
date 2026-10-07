module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.CoherentCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Normal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap111.Exercise_111_54_3_Hypersurface
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_AffineChart

/-!
# Normalization of a plane curve and the divisor of the canonical form

The abstract curve `C` is the normalization of `D = V₊(F)`, with canonical map
`C ⟶ D`, and `K_C` is characterized as the Weil divisor of zeros and poles of
the canonical Kähler form.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The plane curve `V₊(F)` as a scheme over `k`. -/
abbrev planeCurveOver {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    SchemeOverField k :=
  Over.mk (hom d F hF)

/-- `planeCurveOver d F hF` is the over-object of the structure morphism of `V₊(F)`. -/
theorem planeCurveOver_eq_mk {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    planeCurveOver d F hF = Over.mk (hom d F hF) := sorry

/-- A plane curve `V₊(F)` cut out by an irreducible form is a curve over `k`. -/
instance instCurve_planeCurveOver {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] : Curve (planeCurveOver d F hF) := sorry

/-- The `Proj` model of a plane curve over a field is a Noetherian scheme. -/
instance instIsNoetherian_scheme {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    IsNoetherian (scheme d F hF) := sorry

/-- The abstract curve corresponding to the function field of `V₊(F)` is the
normalization of `D` over `k`. -/
def abstractCurve {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] : SchemeOverField k :=
  SchemeOverField.normalization (planeCurveOver d F hF)

/-- `abstractCurve d F hF` is the normalization of `planeCurveOver d F hF`. -/
theorem abstractCurve_eq_normalization {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    abstractCurve d F hF = SchemeOverField.normalization (planeCurveOver d F hF) := sorry

/-- The normalization of a plane curve remains a curve over `k`. -/
instance instCurve_abstractCurve {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] : Curve (abstractCurve d F hF) := sorry

/-- The abstract curve of an irreducible plane curve is Noetherian. -/
instance instIsNoetherian_abstractCurve {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] : IsNoetherian (abstractCurve d F hF).left := sorry

/-- The canonical normalization morphism `C ⟶ D`. -/
def toVanishing {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    (abstractCurve d F hF).left ⟶ scheme d F hF :=
  (planeCurveOver d F hF).left.normalizationTo

/-- `toVanishing` is the canonical normalization morphism of `D`. -/
theorem toVanishing_eq_normalizationTo {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    toVanishing d F hF = (planeCurveOver d F hF).left.normalizationTo := sorry

/-- The normalization map `C ⟶ D` is surjective. -/
instance instSurjective_toVanishing {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] : Surjective (toVanishing d F hF) := sorry

/-- The normalization map `C ⟶ D` is bijective over the nonsingular locus of `D`. -/
theorem bijOn_regularLocus_toVanishing {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    Set.BijOn (toVanishing d F hF).base
      ((toVanishing d F hF).base ⁻¹' (scheme d F hF).regularLocus)
      (scheme d F hF).regularLocus := sorry

/-- If `D` is nonsingular, then `C ⟶ D` is an isomorphism. -/
instance instIsIso_toVanishing_of_regular {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] [Scheme.Regular (scheme d F hF)] :
    IsIso (toVanishing d F hF) := sorry

/-- If `D` is normal, then `C ⟶ D` is an isomorphism. -/
theorem isIso_toVanishing_of_isNormal {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] (hnormal : (scheme d F hF).isNormal) :
    IsIso (toVanishing d F hF) := sorry

/-- Relative differentials of the abstract curve are invertible. -/
instance instInvertible_differentials_abstractCurve {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom]) := sorry

/-- The standard affine chart `D₊(X 0)` on `P^2`. -/
abbrev planeStandardChart {k : Type u} [Field k] :
    (ProjectiveSpace.scheme k 2).Opens :=
  ProjectiveSpace.coordinateBasicOpen (R := k) 2 0

/-- `planeStandardChart` is the basic open `D₊(X 0)` in `P^2`. -/
theorem planeStandardChart_eq {k : Type u} [Field k] :
    planeStandardChart =
      (ProjectiveSpace.coordinateBasicOpen (R := k) 2 0 :
        (ProjectiveSpace.scheme k 2).Opens) := sorry

/-- The section `X (j.succ) / X 0` on `D₊(X 0) ⊂ P^2`. -/
def planeCoordinateSection {k : Type u} [Field k] (j : Fin 2) :
    Γ(ProjectiveSpace.scheme k 2, planeStandardChart) :=
  (ProjectiveSpace.coordinateBasicOpenIsoAway (R := k) 2 0).hom
    (ProjectiveSpace.coordinateRatio (R := k) 2 0 (Equiv.refl (Fin 2)) j)

/-- `planeCoordinateSection j` is the chart ratio `X (j.succ) / X 0`. -/
theorem planeCoordinateSection_eq {k : Type u} [Field k] (j : Fin 2) :
    planeCoordinateSection j =
      (ProjectiveSpace.coordinateBasicOpenIsoAway (R := k) 2 0).hom
        (ProjectiveSpace.coordinateRatio (R := k) 2 0 (Equiv.refl (Fin 2)) j) := sorry

/-- The inverse image on `C` of the standard affine chart `D₊(X 0)`. -/
def standardChartOpen {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    (abstractCurve d F hF).left.Opens :=
  toVanishing d F hF ⁻¹ᵁ (closedImmersion d F hF ⁻¹ᵁ planeStandardChart)

/-- `standardChartOpen` is the pullback of `D₊(X 0)` along `C ⟶ D ⟶ P^2`. -/
theorem standardChartOpen_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    standardChartOpen d F hF =
      toVanishing d F hF ⁻¹ᵁ (closedImmersion d F hF ⁻¹ᵁ planeStandardChart) := sorry

/-- If the affine chart ring is a domain, then `C ∩ {X 0 ≠ 0}` is nonempty. -/
instance instNonempty_standardChartOpen {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    Nonempty (standardChartOpen d F hF) := sorry

/-- The pullback of `X (j.succ) / X 0` to the standard affine chart of `C`. -/
def standardChartSection {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] (j : Fin 2) :
    Γ((abstractCurve d F hF).left, standardChartOpen d F hF) :=
  ((toVanishing d F hF).app (closedImmersion d F hF ⁻¹ᵁ planeStandardChart)).hom
    (((closedImmersion d F hF).app planeStandardChart).hom (planeCoordinateSection j))

/-- `standardChartSection` is the successive pullback of `planeCoordinateSection`. -/
theorem standardChartSection_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] (j : Fin 2) :
    standardChartSection d F hF j =
      ((toVanishing d F hF).app (closedImmersion d F hF ⁻¹ᵁ planeStandardChart)).hom
        (((closedImmersion d F hF).app planeStandardChart).hom
          (planeCoordinateSection j)) := sorry

/-- The image of `X (j.succ) / X 0` in the function field `k(C)`. -/
def standardChartCoord {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] (j : Fin 2) :
    (abstractCurve d F hF).left.functionField :=
  (abstractCurve d F hF).left.germToFunctionField (standardChartOpen d F hF)
    (standardChartSection d F hF j)

/-- `standardChartCoord d F hF j` is the germ of the pulled-back coordinate section. -/
theorem standardChartCoord_eq_germToFunctionField {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] (j : Fin 2) :
    standardChartCoord d F hF j =
      (abstractCurve d F hF).left.germToFunctionField (standardChartOpen d F hF)
        (standardChartSection d F hF j) := sorry

/-- A `k`-algebra identification of the affine function field with `k(C)`. -/
abbrev fractionFieldAbstractCurveIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :=
  fractionField F ≃ₐ[k] SchemeOverField.functionFieldCommAlg (abstractCurve d F hF)

/-- `e` is the standard `X 0`-chart identification when it sends `x` and `y` to the
images of `X 1 / X 0` and `X 2 / X 0` in `k(C)`. -/
def IsStandardChartIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) : Prop :=
  e (xFrac F) = standardChartCoord d F hF 0 ∧
    e (yFrac F) = standardChartCoord d F hF 1

/-- Unfold `IsStandardChartIdent` into the two coordinate identities. -/
theorem isStandardChartIdent_iff {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) :
    IsStandardChartIdent d F hF e ↔
      e (xFrac F) = standardChartCoord d F hF 0 ∧
        e (yFrac F) = standardChartCoord d F hF 1 := sorry

/-- There is a standard `X 0`-chart identification `K ≃ₐ[k] k(C)`. -/
theorem exists_isStandardChartIdent {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    ∃ e, IsStandardChartIdent d F hF e := sorry

/-- A standard `X 0`-chart identification is unique. -/
theorem eq_of_isStandardChartIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    {e e' : fractionFieldAbstractCurveIdent d F hF}
    (he : IsStandardChartIdent d F hF e) (he' : IsStandardChartIdent d F hF e') :
    e = e' := sorry

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
        (canonicalForm F) := sorry

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
        (abstractCurve d F hF).hom.toShHom := sorry

/-- The image of an element of `K` in `k(C)` along a function-field identification. -/
def identApply {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) (a : fractionField F) :
    (abstractCurve d F hF).left.functionField :=
  e a

/-- `identApply` is evaluation of the identification on `K`. -/
theorem identApply_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (e : fractionFieldAbstractCurveIdent d F hF) (a : fractionField F) :
    identApply d F hF e a = e a := sorry

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
        CommRingCat.KaehlerDifferential.d (identApply d F hF e (xFrac F)) := sorry

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
        (canonicalFormStalkTarget d F hF e) := sorry

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
              (Ω[(abstractCurve d F hF).hom.toShHom]) s hs := sorry

/-- There is a unique Weil divisor of zeros and poles of `canonicalForm F` on `C`. -/
theorem existsUnique_zerosPolesDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    ∃! W, IsZerosPolesDivisor d F hF W := sorry

/-- The canonical divisor `K_C` is the unique divisor of zeros and poles of `canonicalForm F`. -/
def canonicalDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    WeilDivisor (abstractCurve d F hF).left :=
  Classical.choose (ExistsUnique.exists (existsUnique_zerosPolesDivisor d F hF))

/-- `canonicalDivisor d F hF` is a divisor of zeros and poles of `canonicalForm F`. -/
theorem canonicalDivisor_spec {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])] :
    IsZerosPolesDivisor d F hF (canonicalDivisor d F hF) := sorry

/-- A divisor of zeros and poles of `canonicalForm F` equals `canonicalDivisor d F hF`. -/
theorem eq_canonicalDivisor {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    [IsLocallyNoetherian (abstractCurve d F hF).left]
    [IsIntegral (abstractCurve d F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve d F hF).hom.toShHom])]
    {W : WeilDivisor (abstractCurve d F hF).left}
    (hW : IsZerosPolesDivisor d F hF W) :
    W = canonicalDivisor d F hF := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
