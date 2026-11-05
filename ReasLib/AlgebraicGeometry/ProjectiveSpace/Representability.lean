/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Datum
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MorphismDatum
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections

/-!
# Representability of projective-space section data

This file compares finite generating families of sections with the degree-one projective-spectrum
construction and states their natural representability by integral projective space.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

/-- The coordinate `T_i`, regarded as a global section of the actual Serre sheaf `O(1)`.
The section is the homogeneous fraction `T_i / 1`, restricted to each open. -/
noncomputable def universalSection (n : ℕ) (i : Fin (n + 1)) :
    (twistingSheaf ℤ n 1).sections :=
  RingedSpace.sectionFromTop (twistingSheaf ℤ n 1)
    (Proj.AssociatedModule.twistSection (grading ℤ n)
      ⟨coordinate (R := ℤ) n i, MvPolynomial.isHomogeneous_X ℤ i⟩)

/-- The coordinate sections generate the actual Serre sheaf `O(1)`: on `D₊(T_i)`
the section `T_i` trivializes this sheaf. -/
theorem universalSections_generate (n : ℕ) :
    Epi (ProjectiveSpaceDatum.sectionFamilyHom (twistingSheaf ℤ n 1) n
      (universalSection n)) := sorry

/-- The canonical universal projective-space datum `(O(1), T_0, ..., T_n)`.
Both the module and its sections are constructed independently of representability. -/
noncomputable def universalDatum (n : ℕ) : ProjectiveSpaceDatum n (scheme ℤ n) where
  lineBundle := twistingSheaf ℤ n 1
  invertible_lineBundle := inferInstance
  sections := universalSection n
  generates := universalSections_generate n

/-- The standard coordinate sections extracted from degree-one projective-spectrum morphism
data for integral projective space. -/
noncomputable def degreeOneSectionFamily {Y : Scheme} (n : ℕ)
    (τ : Proj.DegreeOneMorphismDatum (grading ℤ n) Y) :
    Fin (n + 1) → τ.lineBundle.sections :=
  fun i ↦
    @veroneseDegreeOneSectionFamily
      (MvPolynomial (Fin (n + 1)) ℤ)
      (Submodule ℤ (MvPolynomial (Fin (n + 1)) ℤ)) _ _ _
      (grading ℤ n) _ Y 1 τ.lineBundle τ.lineBundle_invertible τ.sectionMap
      ⟨coordinate (R := ℤ) n i, coordinate_mem_grading_one (R := ℤ) n i⟩

end ProjectiveSpace

namespace ProjectiveSpaceDatum

/-- A finite generating section family agrees with degree-one projective-spectrum data when an
isomorphism of their invertible module sheaves identifies every corresponding section. -/
def RelatesToDegreeOneDatum {Y : Scheme} (n : ℕ)
    (τ : ProjectiveSpaceDatum n Y)
    (σ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading ℤ n) Y) : Prop :=
  ∃ β : τ.lineBundle ≅ σ.lineBundle,
    ∀ i : Fin (n + 1),
      SheafOfModules.sectionsMap β.hom (τ.sections i) =
        ProjectiveSpace.degreeOneSectionFamily n σ i

end ProjectiveSpaceDatum

namespace ProjectiveSpaceDatumClass

/-- A projective-space datum class is associated to a morphism when it has a representative
whose sections agree with degree-one projective-spectrum data associated to that morphism. -/
def AssociatedTo {Y : Scheme} (n : ℕ) (τ : ProjectiveSpaceDatumClass n Y)
    (φ : Y ⟶ ProjectiveSpace.scheme ℤ n) : Prop :=
  ∃ τ' : ProjectiveSpaceDatum n Y,
    (⟦τ'⟧ : ProjectiveSpaceDatumClass n Y) = τ ∧
      ∃ σ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading ℤ n) Y,
        ProjectiveSpaceDatum.RelatesToDegreeOneDatum n τ' σ ∧
          Proj.DegreeOneMorphismDatum.AssociatedTo (ProjectiveSpace.grading ℤ n) σ φ

/-- Association of a represented datum class is equivalent to association through degree-one
projective-spectrum data with the same indexed sections. -/
theorem associatedTo_mk_iff {Y : Scheme} (n : ℕ) (τ : ProjectiveSpaceDatum n Y)
    (φ : Y ⟶ ProjectiveSpace.scheme ℤ n) :
    AssociatedTo n (⟦τ⟧ : ProjectiveSpaceDatumClass n Y) φ ↔
      ∃ σ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading ℤ n) Y,
        ProjectiveSpaceDatum.RelatesToDegreeOneDatum n τ σ ∧
          Proj.DegreeOneMorphismDatum.AssociatedTo (ProjectiveSpace.grading ℤ n) σ φ := sorry

/-- Association is natural under pullback along a morphism of schemes. -/
theorem associatedTo_pullback {X Y : Scheme} (n : ℕ) (f : X ⟶ Y)
    (τ : ProjectiveSpaceDatumClass n Y) (φ : Y ⟶ ProjectiveSpace.scheme ℤ n) :
    AssociatedTo n τ φ → AssociatedTo n (map n f.op τ) (f ≫ φ) := sorry

end ProjectiveSpaceDatumClass

/-- Projective-space datum classes and morphisms into integral projective space determine one
another uniquely through their associated degree-one data. -/
theorem projectiveSpaceDatumClass_associatedTo_bijective (n : ℕ) (Y : Scheme) :
    (∀ τ : ProjectiveSpaceDatumClass n Y,
      ∃! φ : Y ⟶ ProjectiveSpace.scheme ℤ n,
        ProjectiveSpaceDatumClass.AssociatedTo n τ φ) ∧
    (∀ φ : Y ⟶ ProjectiveSpace.scheme ℤ n,
      ∃! τ : ProjectiveSpaceDatumClass n Y,
        ProjectiveSpaceDatumClass.AssociatedTo n τ φ) := sorry

/-- Every projective-space datum class determines a unique morphism into integral projective
space. -/
theorem existsUnique_projectiveSpaceMorphism_of_projectiveSpaceDatumClass
    (n : ℕ) (Y : Scheme) (τ : ProjectiveSpaceDatumClass n Y) :
    ∃! φ : Y ⟶ ProjectiveSpace.scheme ℤ n,
      ProjectiveSpaceDatumClass.AssociatedTo n τ φ :=
  (projectiveSpaceDatumClass_associatedTo_bijective n Y).1 τ

/-- Every morphism into integral projective space determines a unique projective-space datum
class. -/
theorem existsUnique_projectiveSpaceDatumClass_of_projectiveSpaceMorphism
    (n : ℕ) (Y : Scheme) (φ : Y ⟶ ProjectiveSpace.scheme ℤ n) :
    ∃! τ : ProjectiveSpaceDatumClass n Y,
      ProjectiveSpaceDatumClass.AssociatedTo n τ φ :=
  (projectiveSpaceDatumClass_associatedTo_bijective n Y).2 φ

namespace ProjectiveSpaceDatumClass

/-- The class of the canonical datum `(O(1), T_0, ..., T_n)` on integral projective space. -/
def universalClass (n : ℕ) : ProjectiveSpaceDatumClass n (ProjectiveSpace.scheme ℤ n) :=
  ⟦ProjectiveSpace.universalDatum n⟧

/-- The explicitly constructed coordinate datum represents projective-space section data.
This is a proposition, not a choice of a classifying morphism or of an inverse bijection. -/
theorem universalClass_isRepresentedBy (n : ℕ) :
    (functor n).IsRepresentedBy (universalClass n) := sorry

/-- Integral projective `n`-space represents the functor of invertible module sheaves equipped
with `n + 1` generating global sections, modulo section-preserving isomorphism. -/
theorem isRepresentedBy_projectiveSpace (n : ℕ) :
    ∃ x : (functor n).obj (Opposite.op (ProjectiveSpace.scheme ℤ n)),
      (functor n).IsRepresentedBy x :=
  ⟨universalClass n, universalClass_isRepresentedBy n⟩

end ProjectiveSpaceDatumClass

end AlgebraicGeometry
