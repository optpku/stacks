/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
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

/-- The homogeneous ideal of polynomials whose homogeneous components restrict to zero on a
closed subscheme with respect to a chosen twist presentation. -/
def twistIdeal
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    HomogeneousIdeal (ProjectiveSpace.grading R n) where
  carrier := {f | Vanishes n Z P f}
  zero_mem' := Vanishes.zero n Z P
  add_mem' := fun hf hg ↦ Vanishes.add n Z P hf hg
  smul_mem' := fun a _ hf ↦ Vanishes.mul_left n Z P a hf
  is_homogeneous' := fun d _ hf ↦ Vanishes.decompose n Z P hf d

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

/-- The twist-restriction ideal consists exactly of the polynomials vanishing degreewise on the
closed subscheme, and its localizations recover the defining ideals on all standard charts. -/
theorem twistIdeal_spec
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n)) :
    (∀ f : MvPolynomial (Fin (n + 1)) R,
      f ∈ twistIdeal n Z P ↔ Vanishes n Z P f) ∧
      IdealSpec n Z (twistIdeal n Z P) := sorry

end

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
