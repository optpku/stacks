/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.CoordinateIdeal
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.IdealClosure
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Closed subschemes of projective space

Closed subschemes of standard projective space determine homogeneous coordinate ideals by
restricting homogeneous polynomials, viewed as sections of twists, to the closed subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

section

variable {R : Type u} [CommRing R]

/-- The canonical section of the Serre twist associated to a homogeneous polynomial.
Its value at a projective point is the localized fraction with denominator one. -/
def canonicalSectionMap (n d : ℕ) :
    AddCommGrpCat.of (ProjectiveSpace.grading R n d) ⟶
      Scheme.Modules.globalSections (ProjectiveSpace.twistingSheaf R n d) :=
  let φ :=
    Proj.AssociatedModule.degreeZeroToGlobalSections (ProjectiveSpace.grading R n)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (ProjectiveSpace.grading R n)) (d : ℤ))
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ φ ⟨f, by simpa⟩
      map_zero' := φ.map_zero
      map_add' := fun f g ↦ φ.map_add ⟨f, by simpa⟩ ⟨g, by simpa⟩ }

/-- The canonical degree-`d` restriction map used in the definition of `I(Z)` in Stacks
`03GL`. It uses the actual Serre twist, without choosing a twist presentation. -/
abbrev canonicalDegreeMap
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData) (d : ℕ) :
    AddCommGrpCat.of (ProjectiveSpace.grading R n d) ⟶
      Scheme.Modules.globalSections
        ((Scheme.Modules.pullback Z.subschemeι).obj (ProjectiveSpace.twistingSheaf R n d)) :=
  canonicalSectionMap n d ≫
    Scheme.Modules.globalSectionsPullback Z.subschemeι (ProjectiveSpace.twistingSheaf R n d)

/-- Degreewise vanishing for the canonical restriction maps defining `I(Z)`. -/
def CanonicalVanishes
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (f : MvPolynomial (Fin (n + 1)) R) : Prop :=
  ∀ d : ℕ, canonicalDegreeMap n Z d
    (DirectSum.decompose (ProjectiveSpace.grading R n) f d) = 0

/-- The chart-contraction owner of `I(Z)` is the direct sum of the kernels of the
canonical restriction maps to sections of `O_Z(d)`. -/
theorem mem_coordinateIdeal_iff_canonicalVanishes
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (f : MvPolynomial (Fin (n + 1)) R) :
    f ∈ coordinateIdeal n Z ↔ CanonicalVanishes n Z f := sorry

/-- The restriction map from degree-`d` homogeneous polynomials to global sections of the
chosen degree-`d` twist pulled back to a closed subscheme of standard projective space. -/
abbrev degreeMap
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (d : ℕ) :
    AddCommGrpCat.of (ProjectiveSpace.grading R n d) ⟶
      Scheme.Modules.globalSections
        ((Scheme.Modules.pullback Z.subschemeι).obj (P.actualTwist d)) :=
  P.actualSectionMap d ≫
    Scheme.Modules.globalSectionsPullback Z.subschemeι (P.actualTwist d)

/-- A polynomial vanishes on a closed subscheme with respect to a chosen twist presentation
when each homogeneous component restricts to zero. -/
def Vanishes
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (f : MvPolynomial (Fin (n + 1)) R) : Prop :=
  ∀ d : ℕ,
    degreeMap n Z P d
      (DirectSum.decompose (ProjectiveSpace.grading R n) f d) = 0

namespace Vanishes

/-- The zero polynomial vanishes on every closed subscheme. -/
theorem zero
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    Vanishes n Z P 0 := sorry

/-- The sum of two polynomials vanishing on a closed subscheme also vanishes there. -/
theorem add
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    {f g : MvPolynomial (Fin (n + 1)) R}
    (hf : Vanishes n Z P f) (hg : Vanishes n Z P g) :
    Vanishes n Z P (f + g) := sorry

/-- A polynomial multiple of a polynomial vanishing on a closed subscheme also vanishes there. -/
theorem mul_left
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (a : MvPolynomial (Fin (n + 1)) R) {f : MvPolynomial (Fin (n + 1)) R}
    (hf : Vanishes n Z P f) :
    Vanishes n Z P (a • f) := sorry

/-- Every homogeneous component of a polynomial vanishing on a closed subscheme also vanishes
on that subscheme. -/
theorem decompose
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    {f : MvPolynomial (Fin (n + 1)) R} (hf : Vanishes n Z P f) (d : ℕ) :
    Vanishes n Z P
      (DirectSum.decompose (ProjectiveSpace.grading R n) f d) := sorry

end Vanishes

/-- Compatibility view of the intrinsic homogeneous coordinate ideal.

The presentation argument is retained for existing callers; it does not determine the ideal.
The degreewise kernel characterization uses `canonicalDegreeMap`, as recorded in
`twistIdeal_spec`. Vanishing for a separately supplied presentation is `Vanishes`.
-/
def twistIdeal
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    HomogeneousIdeal (ProjectiveSpace.grading R n) where
  toSubmodule := coordinateIdeal n Z
  is_homogeneous' := coordinateIdeal_isHomogeneous n Z

/-- Forgetting the homogeneous compatibility view gives the intrinsic coordinate ideal. -/
@[simp] theorem twistIdeal_toIdeal_eq_coordinateIdeal
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    (twistIdeal n Z P).toIdeal = coordinateIdeal n Z := rfl

/-- A homogeneous ideal cuts out a closed subscheme of standard projective space when, on
every standard coordinate chart, its ordinary localization equals the chart's defining ideal. -/
def IdealSpec
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (I : HomogeneousIdeal (ProjectiveSpace.grading R n)) : Prop :=
  ∀ i : Fin (n + 1),
    Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
      (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
        (Z.ideal
          ((ProjectiveSpace.coordinateBasicOpen (R := R) n i :
            (ProjectiveSpace.scheme R n).affineOpens)))) =
    Ideal.map
      (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (ProjectiveSpace.coordinateLocalizationAway (R := R) n i))
      I.toIdeal

/-- The intrinsic homogeneous ideal recovers the defining ideal on every standard chart. -/
theorem coordinateIdeal_spec
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData) :
    ∀ i : Fin (n + 1),
      Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
        (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
          (Z.ideal (ProjectiveSpace.coordinateBasicOpen (R := R) n i))) =
      Ideal.map
        (algebraMap (MvPolynomial (Fin (n + 1)) R)
          (ProjectiveSpace.coordinateLocalizationAway (R := R) n i))
        (coordinateIdeal n Z) :=
  fun i ↦ (map_coordinateIdeal n Z i).symm

/-- Stacks `03GL`: the closed subscheme is the projective spectrum of its homogeneous
coordinate-ring quotient, compatibly with the given closed immersion.
This is an existence statement in `Prop`; it does not choose an isomorphism as data. -/
theorem coordinateIdeal_quotient_isomorphic
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData) :
    let I : HomogeneousIdeal (ProjectiveSpace.grading R n) :=
      { toSubmodule := coordinateIdeal n Z
        is_homogeneous' := coordinateIdeal_isHomogeneous n Z }
    letI := GradedAlgebra.Quotient.gradedAlgebra
      (ProjectiveSpace.grading R n) I.toIdeal I.isHomogeneous
    Nonempty (Over.mk (projQuotientMap (ProjectiveSpace.grading R n) I) ≅
      Over.mk Z.subschemeι) := sorry

/-- The compatibility ideal has the canonical degreewise kernel characterization and recovers
the defining ideals on all standard charts. No comparison for an arbitrary presentation is
assumed. -/
theorem twistIdeal_spec
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    (∀ f : MvPolynomial (Fin (n + 1)) R,
      f ∈ twistIdeal n Z P ↔ CanonicalVanishes n Z f) ∧
      IdealSpec n Z (twistIdeal n Z P) :=
  ⟨mem_coordinateIdeal_iff_canonicalVanishes n Z, coordinateIdeal_spec n Z⟩

end

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
