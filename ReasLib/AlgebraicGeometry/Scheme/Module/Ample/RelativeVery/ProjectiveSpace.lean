/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Criteria
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative

/-!
# Finite projective-space presentations of relatively very ample modules

This file relates relative very ampleness over an affine base to immersions into finite relative
projective spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- A relatively very ample module for a finite-type morphism to an affine scheme is the pullback
of the tautological module along an immersion over the base into a finite relative projective
space. -/
@[stacks 02NP]
theorem RelativelyVeryAmple.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase
    [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ∃ e : (L ≅ (Scheme.Modules.pullback i).obj P.tautologicalSheaf),
        IsImmersion i ∧ (i ≫ (P.hom) = f) := sorry

/-- A relatively very ample module for a finite-type morphism to an affine scheme admits a
presentation by an immersion into a finite relative projective space and its tautological
module. -/
@[stacks 02NP]
theorem RelativelyVeryAmple.exists_projectiveSpacePresentation_of_finiteType_affineBase
    [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      RelativelyVeryAmplePresentation f L P.hom (ProjectiveSpaceOver.standardModule S n)
        P.isProjectiveBundle i := by
  rcases hL.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase with
    ⟨n, P, i, e, hi, hcomp⟩
  exact ⟨n, P, i, ⟨hi, hcomp, ⟨e⟩⟩⟩

/-- A relatively very ample module for a finite-type morphism to an affine scheme yields an
immersion over the base into a finite relative projective space. -/
theorem RelativelyVeryAmple.exists_projectiveSpaceImmersion_of_finiteType_affineBase
    [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      IsImmersion i ∧ (i ≫ (P.hom) = f) := by
  rcases hL.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase with
    ⟨n, P, i, _, hi, hcomp⟩
  exact ⟨n, P, i, hi, hcomp⟩

/-- An invertible module for a finite-type morphism is relatively very ample exactly when it
admits finite relative projective-space presentations over the members of a base-open cover. -/
@[stacks 02NQ]
theorem RelativelyVeryAmple.iff_exists_openCover_projectiveSpacePresentation_of_finiteType
    [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f] :
    RelativelyVeryAmple f L ↔
      ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
        ∀ j : ι,
          ∃ (n : ℕ) (P : ProjectiveSpaceOver (V j).toScheme n)
            (i : (f ⁻¹ᵁ V j).toScheme ⟶ P.scheme),
            RelativelyVeryAmplePresentation (f ∣_ V j)
              (restrictToBasePreimage f L (V j)) P.hom
              (ProjectiveSpaceOver.standardModule (V j).toScheme n)
              P.isProjectiveBundle i := sorry

end

end AlgebraicGeometry
