/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
import Mathlib.Tactic.CrossRefAttribute

/-!
# The affine complement of one in the projective line

This file owns the non-coordinate chart `D₊(Y - X)`, its explicit affine-line presentation, and
its relation to the standard points `0`, `∞`, and `1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

section CommRing

variable (R : Type u) [CommRing R]

/-- The affine open `D₊(Y - X)` on the projective line. -/
@[stacks 01JE "standard affine complement of one"]
abbrev awayOne : (scheme R).Opens :=
  ProjectiveSpace.basicOpen (R := R) 1 (y R - x R)

/-- The linear form `Y - X` has degree one in the standard grading. -/
@[stacks 01JE "complement-of-one linear form degree"]
theorem y_sub_x_mem_grading_one : y R - x R ∈ grading R 1 := sorry

namespace AwayOne

/-- The degree-zero homogeneous localization defining `D₊(Y - X)`. -/
@[stacks 01JE "complement-of-one section ring"]
abbrev ring := HomogeneousLocalization.Away (grading R) (y R - x R)

/-- The ordinary localization of the homogeneous coordinate ring away from `Y - X`. -/
@[stacks 01JE "complement-of-one ordinary localization"]
abbrev localization := Localization.Away (y R - x R)

/-- The canonical map from the degree-zero homogeneous localization to the ordinary
localization. -/
@[stacks 01JE "complement-of-one localization comparison"]
abbrev toLocalization : ring R →+* localization R :=
  algebraMap (ring R) (localization R)

/-- The coefficient map into the degree-zero localization away from `Y - X`. -/
@[stacks 01JE "complement-of-one coefficient map"]
abbrev coefficientMap : R →+* ring R :=
  (HomogeneousLocalization.fromZeroRingHom
      (grading R) (Submonoid.powers (y R - x R))).comp
    (algebraMap R (grading R 0))

/-- The polynomial coordinate on the affine-line model of `D₊(Y - X)`. -/
@[stacks 01JE "complement-of-one affine coordinate"]
abbrev affineCoordinate : MvPolynomial (ULift.{u} (Fin 1)) R :=
  MvPolynomial.X (ULift.up (0 : Fin 1))

/-- Dehomogenization along `Y - X`, determined by `X ↦ s` and `Y ↦ s + 1`. -/
@[stacks 01JE "complement-of-one dehomogenization"]
noncomputable def dehomogenize :
    MvPolynomial (Fin 2) R →+* MvPolynomial (ULift.{u} (Fin 1)) R :=
  MvPolynomial.eval₂Hom (algebraMap R (MvPolynomial (ULift.{u} (Fin 1)) R)) fun i ↦
    if i = (0 : Fin 2) then affineCoordinate R else affineCoordinate R + 1

/-- Dehomogenization sends `X` to the affine coordinate `s`. -/
@[simp, stacks 01JE "complement-of-one dehomogenization on X"]
theorem dehomogenize_x : dehomogenize R (x R) = affineCoordinate R := sorry

/-- Dehomogenization sends `Y` to `s + 1`. -/
@[simp, stacks 01JE "complement-of-one dehomogenization on Y"]
theorem dehomogenize_y : dehomogenize R (y R) = affineCoordinate R + 1 := sorry

/-- The distinguished linear form `Y - X` becomes `1` under dehomogenization. -/
@[simp, stacks 01JE "complement-of-one dehomogenization denominator"]
theorem dehomogenize_linearForm : dehomogenize R (y R - x R) = 1 := sorry

/-- The distinguished linear form `Y - X` becomes a unit under dehomogenization. -/
@[stacks 01JE "complement-of-one dehomogenization unit"]
theorem dehomogenize_linearForm_isUnit :
    IsUnit (dehomogenize R (y R - x R)) := sorry

/-- The affine coordinate `s = X / (Y - X)` in the degree-zero homogeneous localization. -/
@[stacks 01JE "complement-of-one localized coordinate"]
noncomputable def coordinate : ring R :=
  HomogeneousLocalization.Away.isLocalizationElem
    (sub_mem
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))

/-- The polynomial map sending the affine variable to `X / (Y - X)`. -/
@[stacks 01JE "complement-of-one chart homomorphism"]
noncomputable def chartHom : MvPolynomial (ULift.{u} (Fin 1)) R →+* ring R :=
  MvPolynomial.eval₂Hom (coefficientMap R) fun _ ↦ coordinate R

/-- The chart map sends its polynomial variable to `X / (Y - X)`. -/
@[simp, stacks 01JE "complement-of-one chart coordinate"]
theorem chartHom_X (i : ULift.{u} (Fin 1)) :
    chartHom R (MvPolynomial.X i) = coordinate R := sorry

/-- The explicit dehomogenization map from the chart ring of `D₊(Y - X)` to its affine
polynomial coordinates. -/
@[stacks 01JE "affine complement of one dehomogenization"]
noncomputable def dehomogenization :
    ring R →+* MvPolynomial (ULift.{u} (Fin 1)) R :=
  (Localization.awayLift (dehomogenize R) (y R - x R)
      (dehomogenize_linearForm_isUnit R)).comp (toLocalization R)

/-- Dehomogenization after substitution of the affine coordinate is the identity. -/
@[stacks 01JE "complement-of-one dehomogenization left inverse"]
theorem dehomogenization_comp_chartHom :
    (dehomogenization R).comp (chartHom R) =
      RingHom.id (MvPolynomial (ULift.{u} (Fin 1)) R) := sorry

/-- Substitution of the affine coordinate after dehomogenization is the identity. -/
@[stacks 01JE "complement-of-one dehomogenization right inverse"]
theorem chartHom_comp_dehomogenization :
    (chartHom R).comp (dehomogenization R) = RingHom.id (ring R) := sorry

/-- The explicit ring equivalence identifying the chart ring of `D₊(Y - X)` with an affine
polynomial ring. -/
@[stacks 01JE "affine complement of one chart ring equivalence"]
noncomputable def ringEquiv :
    ring R ≃+* MvPolynomial (ULift.{u} (Fin 1)) R :=
  RingEquiv.ofRingHom (dehomogenization R) (chartHom R)
    (dehomogenization_comp_chartHom R) (chartHom_comp_dehomogenization R)

/-- The forward homomorphism of the explicit chart-ring equivalence is dehomogenization. -/
@[simp, stacks 01JE "complement-of-one ring equivalence forward map"]
theorem ringEquiv_toRingHom :
    (ringEquiv R).toRingHom = dehomogenization R := sorry

/-- The inverse homomorphism of the explicit chart-ring equivalence substitutes the affine
coordinate by `X / (Y - X)`. -/
@[simp, stacks 01JE "complement-of-one ring equivalence inverse map"]
theorem ringEquiv_symm_toRingHom :
    (ringEquiv R).symm.toRingHom = chartHom R := sorry

/-- The inverse homomorphism of the explicit chart-ring equivalence, viewed in `CommRingCat`. -/
@[stacks 01JE "affine complement of one chart ring comparison"]
noncomputable abbrev ringComparison :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) R) ⟶ CommRingCat.of (ring R) :=
  (ringEquiv R).toCommRingCatIso.inv

/-- The chart-ring comparison is substitution of the affine coordinate by
`X / (Y - X)`. -/
@[simp, stacks 01JE "complement-of-one ring comparison map"]
theorem ringComparison_hom : (ringComparison R).hom = chartHom R := sorry

/-- The canonical homogeneous-localization identification of the section ring on
`D₊(Y - X)`. -/
@[stacks 01JE "affine complement of one localized sections"]
noncomputable def ringSectionsIso :
    CommRingCat.of (ring R) ≅ Γ(scheme R, awayOne R) :=
  Proj.basicOpenIsoAway (grading R) (y R - x R)
    (sub_mem
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
    Nat.zero_lt_one

/-- The forward map of the homogeneous-localization section-ring identification. -/
@[stacks 01JE "affine complement of one localized sections comparison"]
noncomputable abbrev ringSectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, awayOne R) :=
  (ringSectionsIso R).hom

/-- The canonical localized comparison agrees with Mathlib's `Proj.awayToSection` map. -/
@[simp, stacks 01JE "affine complement localized sections comparison readout"]
theorem ringSectionsComparison_eq_awayToSection :
    ringSectionsComparison R = Proj.awayToSection (grading R) (y R - x R) := sorry

/-- The canonical isomorphism from the affine polynomial ring to global sections on
`D₊(Y - X)`. -/
@[stacks 01JE "affine complement of one sections isomorphism"]
noncomputable def sectionsIso :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) R) ≅ Γ(scheme R, awayOne R) :=
  (ringEquiv R).toCommRingCatIso.symm ≪≫
    ringSectionsIso R

/-- The affine coordinate `s` as an actual section on `D₊(Y - X) = P¹ \ {1}`. -/
@[stacks 01JE "coordinate section on the complement of one"]
noncomputable def coordinateSection : Γ(scheme R, awayOne R) :=
  (sectionsIso R).hom (affineCoordinate R)

/-- The homogeneous-localization coordinate `X / (Y - X)` is the distinguished affine
coordinate section. -/
@[simp, stacks 01JE "complement-of-one localized coordinate section"]
theorem ringSectionsComparison_coordinate :
    (ringSectionsComparison R).hom (coordinate R) = coordinateSection R := sorry

/-- Under the polynomial presentation of the section ring on `D₊(Y - X)`, the distinguished
section is the polynomial coordinate. -/
@[simp, stacks 01JE "complement-of-one polynomial coordinate section"]
theorem sectionsIso_affineCoordinate :
    (sectionsIso R).hom (affineCoordinate R) = coordinateSection R := sorry

/-- The forward map of the canonical affine-polynomial sections isomorphism. -/
@[stacks 01JE "affine complement of one sections comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) R) ⟶ Γ(scheme R, awayOne R) :=
  (sectionsIso R).hom

/-- The canonical affine-polynomial comparison is the composition of the polynomial
ring-equivalence comparison with the localized section comparison. -/
@[simp, stacks 01JE "affine complement sections comparison readout"]
theorem sectionsComparison_eq_comp :
    sectionsComparison R =
      (ringEquiv R).toCommRingCatIso.symm.hom ≫ ringSectionsComparison R := sorry

/-- The concrete identification of `D₊(Y - X)` with the affine-line model. -/
@[stacks 01JE "affine complement of one isomorphism"]
noncomputable def iso : (awayOne R).toScheme ≅ affineLine R :=
  Proj.basicOpenIsoSpec (grading R) (y R - x R)
      (sub_mem
        (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
        (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
      Nat.zero_lt_one ≪≫
    (Scheme.Spec.mapIso ((ringEquiv R).toCommRingCatIso.op)).symm ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of R)).symm

/-- The forward morphism of the concrete `D₊(Y - X)` affine-line isomorphism. -/
@[stacks 01JE "affine complement of one comparison"]
noncomputable abbrev affineLineComparison : (awayOne R).toScheme ⟶ affineLine R :=
  (iso R).hom

/-- The affine-line comparison for `D₊(Y - X)` respects the structure maps to `Spec(R)`. -/
@[stacks 01JE "complement-of-one affine comparison over base"]
theorem affineLineComparison_toSpec :
    affineLineComparison R ≫ (affineLine R ↘ Spec (CommRingCat.of R)) =
      (awayOne R).ι ≫ toSpec R := sorry

end AwayOne

/-- The open `D₊(Y - X)` is affine. -/
@[stacks 01JE "complement-of-one affineness"]
theorem awayOne_isAffineOpen : IsAffineOpen (awayOne R) := sorry

/-- The affine open `D₊(Y - X)` bundled with its affineness. -/
@[stacks 01JE "affine complement of one in the projective line"]
noncomputable def awayOneAffine : (scheme R).affineOpens :=
  ⟨awayOne R,
    Proj.isAffineOpen_basicOpen (grading R) (y R - x R)
      (sub_mem
        (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
        (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
      Nat.zero_lt_one⟩

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The affine open `D₊(Y - X)` is the complement of any point satisfying the canonical
`[1 : 1]` specification. -/
@[stacks 01JE "complement-of-one point specification"]
theorem IsOnePoint.awayOne_eq_compl {p : scheme k} (hp : IsOnePoint k p) :
    (awayOne k : Set (scheme k)) = ({p} : Set (scheme k))ᶜ := sorry

/-- A point satisfying the canonical `[1 : 1]` specification does not belong to its affine
complement. -/
@[stacks 01JE "one point outside complement-of-one"]
theorem IsOnePoint.not_mem_awayOne {p : scheme k} (hp : IsOnePoint k p) :
    p ∉ awayOne k := sorry

/-- A point satisfying the canonical `[1 : 0]` specification belongs to `D₊(Y - X)`. -/
@[stacks 01JE "zero point in complement-of-one"]
theorem IsZeroPoint.mem_awayOne {p : scheme k} (hp : IsZeroPoint k p) :
    p ∈ awayOne k := sorry

/-- A point satisfying the canonical `[0 : 1]` specification belongs to `D₊(Y - X)`. -/
@[stacks 01JE "infinity point in complement-of-one"]
theorem IsInfinityPoint.mem_awayOne {p : scheme k} (hp : IsInfinityPoint k p) :
    p ∈ awayOne k := sorry

/-- The affine open `D₊(Y - X)` is the complement of the canonical point `1 = [1 : 1]`. -/
@[stacks 01JE "affine complement of one"]
theorem awayOne_eq_compl_onePoint :
    (awayOne k : Set (scheme k)) = ({onePoint k} : Set (scheme k))ᶜ := sorry

/-- The canonical point `1 = [1 : 1]` does not belong to `D₊(Y - X)`. -/
@[stacks 01JE "one point outside its affine complement"]
theorem onePoint_not_mem_awayOne : onePoint k ∉ awayOne k := sorry

/-- The canonical point `0 = [1 : 0]` belongs to `D₊(Y - X)`. -/
@[stacks 01JE "zero point in affine complement of one"]
theorem zeroPoint_mem_awayOne : zeroPoint k ∈ awayOne k := sorry

/-- The canonical point `∞ = [0 : 1]` belongs to `D₊(Y - X)`. -/
@[stacks 01JE "infinity point in affine complement of one"]
theorem infinityPoint_mem_awayOne : infinityPoint k ∈ awayOne k := sorry

end Field
end AlgebraicGeometry.ProjectiveLine
