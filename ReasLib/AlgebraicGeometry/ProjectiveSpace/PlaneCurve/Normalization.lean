module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Normal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.AffineChart
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span

/-!
# Normalized plane curves and their standard affine coordinates

The normalization of a projective plane hypersurface has a canonical morphism
to that hypersurface. Its standard affine coordinates identify the fraction
field of the affine equation with the function field of the normalization.
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
  Over.mk (Hypersurface.hom 2 d F hF)

/-- `planeCurveOver d F hF` is the over-object of the structure morphism of `V₊(F)`. -/
theorem planeCurveOver_eq_mk {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    planeCurveOver d F hF = Over.mk (Hypersurface.hom 2 d F hF) := rfl

/-- A plane curve `V₊(F)` cut out by an irreducible form is a curve over `k`. -/
instance instCurve_planeCurveOver {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] : Curve (planeCurveOver d F hF) := sorry

/-- The `Proj` model of a plane curve over a field is a Noetherian scheme. -/
instance instIsNoetherian_scheme {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    IsNoetherian (Hypersurface.scheme 2 d F hF) := sorry

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
    abstractCurve d F hF = SchemeOverField.normalization (planeCurveOver d F hF) := rfl

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
    (abstractCurve d F hF).left ⟶ Hypersurface.scheme 2 d F hF :=
  (planeCurveOver d F hF).left.normalizationTo

/-- `toVanishing` is the canonical normalization morphism of `D`. -/
theorem toVanishing_eq_normalizationTo {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    toVanishing d F hF = (planeCurveOver d F hF).left.normalizationTo := rfl

/-- The normalization map `C ⟶ D` is surjective. -/
instance instSurjective_toVanishing {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] : Surjective (toVanishing d F hF) :=
  Scheme.Normalization.surjective (planeCurveOver d F hF).left

/-- The normalization map `C ⟶ D` is bijective over the nonsingular locus of `D`. -/
theorem bijOn_regularLocus_toVanishing {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    Set.BijOn (toVanishing d F hF).base
      ((toVanishing d F hF).base ⁻¹' (Hypersurface.scheme 2 d F hF).regularLocus)
      (Hypersurface.scheme 2 d F hF).regularLocus := sorry

/-- If `D` is nonsingular, then `C ⟶ D` is an isomorphism. -/
instance instIsIso_toVanishing_of_regular {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] [Scheme.Regular (Hypersurface.scheme 2 d F hF)] :
    IsIso (toVanishing d F hF) := sorry

/-- The standard affine chart `D₊(X 0)` on `P^2`. -/
abbrev planeStandardChart {k : Type u} [Field k] :
    (ProjectiveSpace.scheme k 2).Opens :=
  ProjectiveSpace.coordinateBasicOpen (R := k) 2 0

/-- `planeStandardChart` is the basic open `D₊(X 0)` in `P^2`. -/
theorem planeStandardChart_eq {k : Type u} [Field k] :
    planeStandardChart =
      (ProjectiveSpace.coordinateBasicOpen (R := k) 2 0 :
        (ProjectiveSpace.scheme k 2).Opens) := rfl

/-- The section `X (j.succ) / X 0` on `D₊(X 0) ⊂ P^2`. -/
def planeCoordinateSection {k : Type u} [Field k] (j : Fin 2) :
    Γ(ProjectiveSpace.scheme k 2, planeStandardChart) :=
  (ProjectiveSpace.coordinateBasicOpenIsoAway (R := k) 2 0).hom
    (ProjectiveSpace.coordinateRatio (R := k) 2 0 (Equiv.refl (Fin 2)) j)

/-- `planeCoordinateSection j` is the chart ratio `X (j.succ) / X 0`. -/
theorem planeCoordinateSection_eq {k : Type u} [Field k] (j : Fin 2) :
    planeCoordinateSection j =
      (ProjectiveSpace.coordinateBasicOpenIsoAway (R := k) 2 0).hom
        (ProjectiveSpace.coordinateRatio (R := k) 2 0 (Equiv.refl (Fin 2)) j) := rfl

/-- The inverse image on `C` of the standard affine chart `D₊(X 0)`. -/
def standardChartOpen {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    (abstractCurve d F hF).left.Opens :=
  toVanishing d F hF ⁻¹ᵁ (Hypersurface.closedImmersion 2 d F hF ⁻¹ᵁ planeStandardChart)

/-- `standardChartOpen` is the pullback of `D₊(X 0)` along `C ⟶ D ⟶ P^2`. -/
theorem standardChartOpen_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    standardChartOpen d F hF =
      toVanishing d F hF ⁻¹ᵁ (Hypersurface.closedImmersion 2 d F hF ⁻¹ᵁ planeStandardChart) := rfl

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
  ((toVanishing d F hF).app (Hypersurface.closedImmersion 2 d F hF ⁻¹ᵁ planeStandardChart)).hom
    (((Hypersurface.closedImmersion 2 d F hF).app planeStandardChart).hom (planeCoordinateSection j))

/-- `standardChartSection` is the successive pullback of `planeCoordinateSection`. -/
theorem standardChartSection_eq {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] (j : Fin 2) :
    standardChartSection d F hF j =
      ((toVanishing d F hF).app (Hypersurface.closedImmersion 2 d F hF ⁻¹ᵁ planeStandardChart)).hom
        (((Hypersurface.closedImmersion 2 d F hF).app planeStandardChart).hom
          (planeCoordinateSection j)) := rfl

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
        (standardChartSection d F hF j) := rfl

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
        e (yFrac F) = standardChartCoord d F hF 1 := Iff.rfl

/-- A standard `X 0`-chart identification is unique. -/
theorem eq_of_isStandardChartIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    {e e' : fractionFieldAbstractCurveIdent d F hF}
    (he : IsStandardChartIdent d F hF e) (he' : IsStandardChartIdent d F hF e') :
    e = e' := sorry

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
    identApply d F hF e a = e a := rfl

/-- If a projective plane hypersurface is a curve and its standard affine
coordinate ring is a domain, its affine defining equation is irreducible. -/
theorem irreducible_affineEquation_of_curve {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    Irreducible (affineEquation F) := sorry

/-- Evaluation of the affine equation at the pulled-back standard coordinates vanishes. -/
theorem standardChart_eval_affineEquation {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    MvPolynomial.aeval
      (S₁ := SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
      (fun j => standardChartCoord d F hF j)
      (affineEquation F) = 0 := sorry

/-- The affine coordinate algebra maps to the normalized curve's function field
by evaluating its variables at the pulled-back standard coordinates. -/
def standardChartCoordinateHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    affineCoordinateRing F →ₐ[k] SchemeOverField.functionFieldCommAlg (abstractCurve d F hF) :=
  Ideal.Quotient.liftₐ (Ideal.span {affineEquation F})
    (MvPolynomial.aeval
      (S₁ := SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
      (fun j => standardChartCoord d F hF j)) (by
      intro p hp
      have hker : Ideal.span {affineEquation F} ≤
          RingHom.ker (MvPolynomial.aeval
            (S₁ := SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
            (fun j => standardChartCoord d F hF j)).toRingHom := by
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        exact standardChart_eval_affineEquation d F hF
      exact hker hp)

/-- Evaluation at the standard coordinates embeds the affine coordinate algebra
in the function field of the normalization. -/
theorem standardChartCoordinateHom_injective {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    Function.Injective (standardChartCoordinateHom d F hF) := sorry

/-- The standard coordinate homomorphism extends to the fraction field by its
universal property. -/
def standardChartFractionHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    fractionField F →ₐ[k] SchemeOverField.functionFieldCommAlg (abstractCurve d F hF) :=
  @IsFractionRing.liftAlgHom k _ (affineCoordinateRing F) _ (fractionField F) _
    (SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))
    (inferInstanceAs (Field (abstractCurve d F hF).left.functionField))
    _ _ _ _ _ (SchemeOverField.functionFieldAlgebra (abstractCurve d F hF))
    (standardChartCoordinateHom d F hF)
    (standardChartCoordinateHom_injective d F hF)

/-- The standard coordinate fraction-field homomorphism is bijective. -/
theorem standardChartFractionHom_bijective {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    Function.Bijective (standardChartFractionHom d F hF) := sorry

/-- The fraction field of the affine equation is identified with the normalized
curve's function field by the standard coordinate homomorphism. -/
def standardChartIdent {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    fractionFieldAbstractCurveIdent d F hF :=
  AlgEquiv.ofBijective (standardChartFractionHom d F hF)
    (standardChartFractionHom_bijective d F hF)

/-- The standard field identification sends the affine coordinates to the
corresponding pulled-back coordinate germs. -/
theorem standardChartIdent_spec {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    IsStandardChartIdent d F hF (standardChartIdent d F hF) := sorry

/-- There is an identification of the affine function field with the normalized
curve's function field sending both affine coordinates to their standard germs. -/
theorem exists_isStandardChartIdent {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)] :
    ∃ e, IsStandardChartIdent d F hF e :=
  ⟨standardChartIdent d F hF, standardChartIdent_spec d F hF⟩

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
