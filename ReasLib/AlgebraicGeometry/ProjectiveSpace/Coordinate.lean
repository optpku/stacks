/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard projective coordinates

The coordinate charts of standard projective space are described through homogeneous
localizations and identified explicitly with affine space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.ProjectiveSpace

section

variable {R : Type u} [CommRing R]

/-- The basic open `D₊(f)` in standard projective space for the standard polynomial grading. -/
@[stacks 01JE "projective basic open"]
abbrev basicOpen (n : ℕ) (f : MvPolynomial (Fin (n + 1)) R) :
    (scheme R n).Opens :=
  Proj.basicOpen (grading R n) f

/-- A standard projective-space basic open is affine when its defining polynomial is
homogeneous of positive degree. -/
@[stacks 01JE "projective basic-open affineness"]
theorem basicOpen_isAffineOpen (n : ℕ) (f : MvPolynomial (Fin (n + 1)) R)
    (d : ℕ) (hf : f ∈ grading R n d) (hd : 0 < d) :
    IsAffineOpen (basicOpen n f) := sorry

/-- The homogeneous coordinate `T_i` on standard projective `n`-space. -/
@[stacks 01JE "homogeneous coordinate"]
abbrev coordinate (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.X i

/-- The coordinate polynomial `T_i` has degree `1` in the standard grading on
`R[T_0, ..., T_n]`. -/
@[stacks 01JE "homogeneous coordinate degree"]
theorem coordinate_mem_grading_one (n : ℕ) (i : Fin (n + 1)) :
    coordinate (R := R) n i ∈ grading R n 1 := sorry

/-- The standard chart `D₊(T_i)` on `scheme R n` is affine. -/
@[stacks 01JE "projective coordinate chart affineness"]
theorem coordinateBasicOpen_isAffineOpen (n : ℕ) (i : Fin (n + 1)) :
    IsAffineOpen (basicOpen (R := R) n (coordinate (R := R) n i)) := sorry

/-- The standard affine chart `D₊(T_i)` on `scheme R n`. -/
@[stacks 01JE "projective coordinate chart"]
abbrev coordinateBasicOpen (n : ℕ) (i : Fin (n + 1)) :
    (scheme R n).affineOpens :=
  ⟨basicOpen (R := R) n (coordinate (R := R) n i),
    Proj.isAffineOpen_basicOpen (grading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one⟩

/-- The homogeneous coordinates generate the standard projective coordinate ring over its
degree-zero piece. -/
@[stacks 01JE "projective homogeneous coordinates generate"]
theorem coordinates_generate (n : ℕ) :
    Algebra.adjoin (grading R n 0)
      (Set.range (coordinate (R := R) n)) = ⊤ := sorry

/-- The standard affine coordinate charts cover projective space. -/
@[stacks 01JE "projective coordinate chart cover"]
theorem iSup_coordinateBasicOpen_eq_top (n : ℕ) :
    (⨆ i : Fin (n + 1),
      (coordinateBasicOpen (R := R) n i : (scheme R n).Opens)) = ⊤ := sorry

/-- The degree-zero homogeneous localization away from the coordinate `T_i`. -/
@[stacks 01JE "projective coordinate localization"]
abbrev coordinateAway (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading R n)
    (coordinate (R := R) n i)

/-- The ordinary localization away from the coordinate `T_i`. -/
@[stacks 01JE "projective coordinate ordinary localization"]
abbrev coordinateLocalizationAway (n : ℕ) (i : Fin (n + 1)) :=
  Localization.Away (coordinate (R := R) n i)

/-- The canonical map from the degree-zero localization away from `T_i` to the ordinary
localization away from `T_i`. -/
@[stacks 01JE "projective coordinate localization map"]
abbrev coordinateAwayToLocalization (n : ℕ) (i : Fin (n + 1)) :
    coordinateAway (R := R) n i →+* coordinateLocalizationAway (R := R) n i :=
  algebraMap (coordinateAway (R := R) n i) (coordinateLocalizationAway (R := R) n i)

/-- The canonical ring identification on the standard chart `D₊(T_i)` of `scheme R n`. -/
@[stacks 01JE "projective coordinate chart sections"]
abbrev coordinateBasicOpenIsoAway (n : ℕ) (i : Fin (n + 1)) :
    CommRingCat.of (coordinateAway (R := R) n i) ≅
      Γ(scheme R n, (coordinateBasicOpen (R := R) n i : (scheme R n).Opens)) :=
  Proj.basicOpenIsoAway (grading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

/-- The coefficient map into the degree-zero homogeneous localization on `D₊(T_i)`. -/
@[stacks 01JE "projective coordinate coefficient map"]
abbrev coefficientToCoordinateAway (n : ℕ) (i : Fin (n + 1)) :
    R →+* coordinateAway (R := R) n i :=
  (HomogeneousLocalization.fromZeroRingHom
      (grading R n)
      (Submonoid.powers (coordinate (R := R) n i))).comp
    (algebraMap R (grading R n 0))

/-- Dehomogenization at `T_i`, sending `T_i` to `1` and the remaining coordinates through
`e : Fin n ≃ ι`. -/
@[stacks 01JE "projective chart dehomogenization"]
noncomputable def dehomogenizeAt (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom (algebraMap R (MvPolynomial ι R)) fun j ↦
    if h : j = i then 1 else
      MvPolynomial.X (e ((finSuccAboveEquiv i).symm ⟨j, h⟩))

/-- Dehomogenization at `T_i` sends the distinguished coordinate to `1`. -/
@[simp, stacks 01JE "projective chart dehomogenization coordinate"]
theorem dehomogenizeAt_coordinate_self (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    dehomogenizeAt (R := R) n i e (coordinate (R := R) n i) = 1 := sorry

/-- The distinguished coordinate becomes a unit under dehomogenization. -/
@[stacks 01JE "projective chart dehomogenization unit"]
theorem dehomogenizeAt_coordinate_isUnit (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    IsUnit (dehomogenizeAt (R := R) n i e (coordinate (R := R) n i)) := sorry

/-- The chart coordinate `T_{i.succAbove (e.symm j)} / T_i` in the degree-zero homogeneous
localization. -/
@[stacks 01JE "projective chart coordinate ratio"]
noncomputable def coordinateRatio (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) (j : ι) : coordinateAway (R := R) n i :=
  HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i)
    (MvPolynomial.isHomogeneous_X R (i.succAbove (e.symm j)))

/-- The polynomial chart map sending `x_j` to `T_{i.succAbove (e.symm j)} / T_i`. -/
@[stacks 01JE "projective affine chart homomorphism"]
noncomputable def affineChartHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    MvPolynomial ι R →+* coordinateAway (R := R) n i :=
  MvPolynomial.eval₂Hom (coefficientToCoordinateAway (R := R) n i)
    (coordinateRatio (R := R) n i e)

/-- The affine chart map sends a polynomial variable to the corresponding homogeneous
coordinate ratio. -/
@[simp, stacks 01JE "projective affine chart variable"]
theorem affineChartHom_X (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) (j : ι) :
    affineChartHom (R := R) n i e (MvPolynomial.X j) =
      coordinateRatio (R := R) n i e j := sorry

namespace CoordinateChart

/-- The explicit dehomogenization map from the coordinate chart ring to affine polynomial
coordinates. -/
@[stacks 01JE "projective coordinate-chart dehomogenization"]
noncomputable def dehomogenization (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    coordinateAway (R := R) n i →+* MvPolynomial ι R :=
  (Localization.awayLift (dehomogenizeAt (R := R) n i e)
      (coordinate (R := R) n i)
      (dehomogenizeAt_coordinate_isUnit (R := R) n i e)).comp
    (coordinateAwayToLocalization (R := R) n i)

/-- Dehomogenization after substitution of affine chart coordinates is the identity. -/
@[stacks 01JE "projective chart dehomogenization inverse"]
theorem dehomogenization_comp_affineChartHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (dehomogenization (R := R) n i e).comp (affineChartHom (R := R) n i e) =
      RingHom.id (MvPolynomial ι R) := sorry

/-- Substitution of affine chart coordinates after dehomogenization is the identity. -/
@[stacks 01JE "projective chart rehomogenization inverse"]
theorem affineChartHom_comp_dehomogenization (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (affineChartHom (R := R) n i e).comp (dehomogenization (R := R) n i e) =
      RingHom.id (coordinateAway (R := R) n i) := sorry

/-- The explicit ring equivalence from the degree-zero coordinate localization to affine
polynomial coordinates. -/
@[stacks 01JE "projective coordinate chart ring equivalence"]
noncomputable def ringEquiv (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    coordinateAway (R := R) n i ≃+* MvPolynomial ι R :=
  RingEquiv.ofRingHom (dehomogenization (R := R) n i e)
    (affineChartHom (R := R) n i e)
    (dehomogenization_comp_affineChartHom (R := R) n i e)
    (affineChartHom_comp_dehomogenization (R := R) n i e)

/-- The forward homomorphism of the chart-ring equivalence is dehomogenization. -/
@[simp, stacks 01JE "projective chart ring equivalence forward"]
theorem ringEquiv_toRingHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (ringEquiv (R := R) n i e).toRingHom = dehomogenization (R := R) n i e := sorry

/-- The inverse homomorphism of the chart-ring equivalence substitutes coordinate ratios. -/
@[simp, stacks 01JE "projective chart ring equivalence inverse"]
theorem ringEquiv_symm_toRingHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (ringEquiv (R := R) n i e).symm.toRingHom = affineChartHom (R := R) n i e := sorry

/-- The inverse homomorphism of the explicit chart-ring equivalence, viewed in `CommRingCat`. -/
@[stacks 01JE "projective coordinate chart ring comparison"]
noncomputable abbrev ringComparison (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    CommRingCat.of (MvPolynomial ι R) ⟶
      CommRingCat.of (coordinateAway (R := R) n i) :=
  (ringEquiv (R := R) n i e).toCommRingCatIso.inv

/-- The underlying ring homomorphism of the chart-ring comparison is substitution by coordinate
ratios. -/
@[simp, stacks 01JE "projective coordinate chart ring comparison hom"]
theorem ringComparison_hom (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (ringComparison (R := R) n i e).hom = affineChartHom (R := R) n i e := sorry

/-- The concrete identification of the `i`-th projective chart with affine space after choosing
names for the remaining coordinates. -/
@[stacks 01JE "projective coordinate chart isomorphism with reindexing"]
noncomputable def isoWith (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ≅
      𝔸(ι; Spec (CommRingCat.of R)) :=
  Proj.basicOpenIsoSpec (grading R n) (coordinate (R := R) n i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ≪≫
    (Scheme.Spec.mapIso
      ((ringEquiv (R := R) n i e).toCommRingCatIso.op)).symm ≪≫
    (AffineSpace.SpecIso ι (CommRingCat.of R)).symm

/-- The forward morphism of the concrete chart isomorphism with a chosen coordinate
reindexing. -/
@[stacks 01JE "projective coordinate-chart comparison with reindexing"]
noncomputable abbrev comparisonWith (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ⟶
      𝔸(ι; Spec (CommRingCat.of R)) :=
  (isoWith (R := R) n i e).hom

/-- The concrete identification of the `i`-th standard projective chart with canonical affine
`n`-space. -/
@[stacks 01JE "projective coordinate chart isomorphism"]
noncomputable abbrev iso (n : ℕ) (i : Fin (n + 1)) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ≅
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) :=
  isoWith (R := R) n i Equiv.ulift.symm

/-- The forward morphism of the concrete standard coordinate-chart isomorphism. -/
@[stacks 01JE "projective coordinate chart as affine space"]
noncomputable abbrev comparison (n : ℕ) (i : Fin (n + 1)) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ⟶
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) :=
  (iso (R := R) n i).hom

/-- The standard coordinate-chart comparison respects the structure maps to `Spec(R)`. -/
@[stacks 01JE "projective coordinate-chart structure map"]
theorem comparison_toSpec (n : ℕ) (i : Fin (n + 1)) :
    comparison (R := R) n i ≫
        (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
      (coordinateBasicOpen (R := R) n i).1.ι ≫ toSpec R n := sorry

end CoordinateChart

end

end AlgebraicGeometry.ProjectiveSpace
