/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Curve
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Boundary
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# A non-killable H¹ class on the projective line

The ideal sheaf of `{0, ∞} ⊂ ℙ¹_k` is invertible, and the connecting class of the
indicator section of `i_* 𝒪_Z` at `0` remains nonzero after pullback along every
finite surjective scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.NonkillableClass

variable (k : Type u) [Field k]

/-- The homogeneous zero locus `V(y)` on `ℙ¹_k`, whose unique closed point is `0 = [1 : 0]`. -/
def zeroLocus : Closeds (scheme k) :=
  ⟨ProjectiveSpectrum.zeroLocus (grading k) {y k},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The homogeneous zero locus `V(x)` on `ℙ¹_k`, whose unique closed point is `∞ = [0 : 1]`. -/
def infinityLocus : Closeds (scheme k) :=
  ⟨ProjectiveSpectrum.zeroLocus (grading k) {x k},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The reduced closed subscheme `Z = {0, ∞}` of `ℙ¹_k`, as the scheme-theoretic union of `V(y)`
and `V(x)`. In the ideal-sheaf lattice this is the infimum, equivalently
`vanishingIdeal (zeroLocus k ⊔ infinityLocus k)`. -/
def twoPointDivisor : (scheme k).IdealSheafData :=
  vanishingIdeal (zeroLocus k) ⊓ vanishingIdeal (infinityLocus k)

/-- `twoPointDivisor k` is the vanishing ideal of the closed set `{0, ∞}`. -/
theorem twoPointDivisor_eq :
    twoPointDivisor k = vanishingIdeal (zeroLocus k ⊔ infinityLocus k) := sorry

/-- The support of `twoPointDivisor k` contains the two distinct closed points `0` and `∞`. -/
theorem twoPointDivisor_spec :
    zeroPoint k ∈ (twoPointDivisor k).support ∧
      infinityPoint k ∈ (twoPointDivisor k).support := sorry

/-- The two-point closed subscheme is an effective Cartier divisor on `ℙ¹_k`. -/
instance instIsEffectiveCartierDivisor_twoPointDivisor :
    IsEffectiveCartierDivisor (twoPointDivisor k).subschemeι := sorry

/-- The invertible sheaf `L = I_Z` associated to the ideal sheaf of `{0, ∞}`. -/
@[reducible]
def lineBundle : (scheme k).Modules :=
  (twoPointDivisor k).toModule

/-- `lineBundle k` is the module sheaf of the ideal of `{0, ∞}`. -/
theorem lineBundle_def : lineBundle k = (twoPointDivisor k).toModule := sorry

/-- The canonical complex `0 → I_Z → 𝒪 → i_* 𝒪_Z → 0` on `ℙ¹_k`. -/
def idealSequence : ShortComplex (scheme k).Modules :=
  ShortComplex.mk (twoPointDivisor k).toSubobject.arrow
    (SheafOfModules.unitToPushforwardObjUnit (twoPointDivisor k).subschemeι.toRingCatSheafHom)
    (twoPointDivisor k).toSubobject_arrow_comp_quotient

/-- The first term of `idealSequence k` is `lineBundle k`. -/
theorem idealSequence_X₁ : (idealSequence k).X₁ = lineBundle k := sorry

/-- The middle term of `idealSequence k` is the structure module of `ℙ¹_k`. -/
theorem idealSequence_X₂ :
    (idealSequence k).X₂ = (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) := sorry

/-- The third term of `idealSequence k` is the pushforward `i_* 𝒪_Z`. -/
theorem idealSequence_X₃ :
    (idealSequence k).X₃ = closedSubschemeStructureSheafOn (twoPointDivisor k) := sorry

/-- The ideal sequence of `{0, ∞}` is short exact. -/
theorem idealSequence_shortExact : (idealSequence k).ShortExact := sorry

/-- The standard affine charts `D₊(x)` and `D₊(y)` of `ℙ¹_k`. -/
private abbrev twoPointChart : Fin 2 → (scheme k).Opens :=
  fun i ↦ ProjectiveSpace.coordinateBasicOpen (R := k) 1 i

/-- The inclusions of the standard charts into the top open of `ℙ¹_k`. -/
private abbrev twoPointChartι (i : Fin 2) : twoPointChart k i ⟶ (⊤ : (scheme k).Opens) :=
  homOfLE le_top

/-- The two standard charts cover `ℙ¹_k` in the Zariski topology. -/
private theorem twoPointChart_cover_mem :
    Sieve.ofArrows (twoPointChart k) (twoPointChartι k) ∈
      Opens.grothendieckTopology (scheme k) (⊤ : (scheme k).Opens) := sorry

/-- The additive sheaf `i_* 𝒪_Z` on `ℙ¹_k`. -/
private abbrev twoPointSheaf :=
  (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj
    (closedSubschemeStructureSheafOn (twoPointDivisor k))

/-- The unit section of `i_* 𝒪_{V(y)}`. -/
def unitOnZero :
    Hom.globalSectionsMod (toSpec k)
      (closedSubschemeStructureSheafOn (vanishingIdeal (zeroLocus k))) :=
  (SheafOfModules.pushforwardSections
      (vanishingIdeal (zeroLocus k)).subschemeι.toRingCatSheafHom
      (RingedSpace.unitSectionFromTop
        (vanishingIdeal (zeroLocus k)).subscheme.toRingedSpace
        (RingedSpace.unitTopValue
          (vanishingIdeal (zeroLocus k)).subscheme.toRingedSpace))).1 (op ⊤)

/-- The local section of `i_* 𝒪_Z` that is `1` on `chartX ∩ Z` and `0` on `chartY ∩ Z`. -/
private def indicatorZeroOnChart (i : Fin 2) :
    (twoPointSheaf k).obj.obj (op (twoPointChart k i)) :=
  if i = 0 then
    (SheafOfModules.unitToPushforwardObjUnit
        (twoPointDivisor k).subschemeι.toRingCatSheafHom).val.app
      (op (twoPointChart k i)) (1 : Γ(scheme k, twoPointChart k i))
  else
    0

/-- The local morphisms `ℤ ⟶ (i_* 𝒪_Z)(D₊(xᵢ))` classifying `indicatorZeroOnChart`. -/
private def indicatorZeroOnChartHom (i : Fin 2) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      (twoPointSheaf k).obj.obj (op (twoPointChart k i)) :=
  (AddCommGrpCat.coyonedaObjIsoForget.app
      ((twoPointSheaf k).obj.obj (op (twoPointChart k i)))).inv
    (indicatorZeroOnChart k i)

/-- The local morphisms `1` on `D₊(x)` and `0` on `D₊(y)` agree on overlaps. -/
private theorem indicatorZeroOnChartHom_compatible
    ⦃W : (scheme k).Opens⦄ ⦃i j : Fin 2⦄
    (a : W ⟶ twoPointChart k i) (b : W ⟶ twoPointChart k j)
    (hab : a ≫ twoPointChartι k i = b ≫ twoPointChartι k j) :
    indicatorZeroOnChartHom k i ≫ (twoPointSheaf k).obj.map a.op =
      indicatorZeroOnChartHom k j ≫ (twoPointSheaf k).obj.map b.op := sorry

/-- The global section of `i_* 𝒪_Z` obtained by gluing value `1` on `chartX ∩ Z` and
value `0` on `chartY ∩ Z`. -/
@[no_expose]
def indicatorZero : Hom.globalSectionsMod (toSpec k) (idealSequence k).X₃ :=
  ((twoPointSheaf k).property.amalgamateOfArrows (twoPointChartι k)
      (twoPointChart_cover_mem k) (indicatorZeroOnChartHom k)
      (indicatorZeroOnChartHom_compatible k)).hom
    (ULift.up (1 : ℤ))

/-- The restrictions of `indicatorZero k` along the two closed points are `1` on `V(y)`
and `0` on `V(x)`. -/
theorem indicatorZero_spec :
    (closedSubschemeStructureSheafMap
          (inf_le_left : twoPointDivisor k ≤ vanishingIdeal (zeroLocus k))).val.app (op ⊤)
        (indicatorZero k) =
      unitOnZero k ∧
    (closedSubschemeStructureSheafMap
          (inf_le_right : twoPointDivisor k ≤ vanishingIdeal (infinityLocus k))).val.app (op ⊤)
        (indicatorZero k) =
      0 := sorry

/-- The connecting class `ξ ∈ H¹(ℙ¹_k, L)` of the indicator section of `i_* 𝒪_Z`. -/
def xi : Hom.cohomology (toSpec k) (lineBundle k) 1 :=
  Hom.cohomologyBoundaryFromExt (toSpec k) (idealSequence_shortExact k) (indicatorZero k)

/-- `xi k` is the Ext connecting class of `indicatorZero k`. -/
theorem xi_eq :
    xi k = Hom.cohomologyBoundaryFromExt (toSpec k) (idealSequence_shortExact k)
      (indicatorZero k) := sorry

/-- The connecting class on `ℙ¹_k` is already nonzero. -/
theorem xi_ne_zero : xi k ≠ 0 := sorry

/-- The connecting class of the zero-component indicator on the projective line remains
nonzero after every finite surjective scheme morphism. -/
theorem cohomologyPullback_ne_zero {Y : Scheme.{u}} (π : Y ⟶ scheme k)
    [IsFinite π] [Surjective π] :
    Hom.cohomologyPullback (toSpec k) π (lineBundle k) 1 (xi k) ≠ 0 := sorry

end AlgebraicGeometry.ProjectiveLine.NonkillableClass
