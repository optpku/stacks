/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Homology.DerivedCategory.TruncationFiltration
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Renumbering
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence

/-!
# Truncation spectral sequences for unbounded right-derived functors

The canonical truncation filtration of a representative of `K : DerivedCategory A` gives an
`E₁` spectral sequence.  This file owns its standard simultaneous page-and-bidegree renumbering,
whose second page is `R^i F (H^j K)`.  The construction is independent of ringed spaces and can be
specialized by any downstream right-derived functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- The cycles-to-homology quotient of the upper truncation descends through the cokernel of
the preceding truncation step. It is zero in every degree other than `j`. -/
noncomputable def truncationStepToCohomology (C : CochainComplex A ℤ) (j : ℤ) :
    cokernel (C.truncLEStep j) ⟶ (CochainComplex.singleFunctor A j).obj (C.homology j) :=
  cokernel.desc (C.truncLEStep j)
    (DerivedCategory.ShiftedHom.Boundary.cochainProjection C j) (by
      apply HomologicalComplex.to_single_hom_ext
      exact ((C.truncLE (j - 1)).isZero_of_isStrictlyLE (j - 1) j (by omega)).eq_of_src _ _)

/-- The map out of the cokernel retains the canonical upper-truncation projection. -/
@[reassoc (attr := simp)]
theorem π_truncationStepToCohomology (C : CochainComplex A ℤ) (j : ℤ) :
    cokernel.π (C.truncLEStep j) ≫ truncationStepToCohomology C j =
      DerivedCategory.ShiftedHom.Boundary.cochainProjection C j := by
  simp [truncationStepToCohomology]

variable [HasDerivedCategory.{wA} A]

/-- The canonical comparison from the actual truncation-filtration quotient to the single
cohomology complex. It uses the canonical cokernel comparison and the cycles-to-homology
quotient of the selected representative, followed by its localization homology comparison.
This map is a quasi-isomorphism, rather than an isomorphism of cochain complexes. -/
@[stacks 0BKM "canonical truncation graded-piece comparison"]
noncomputable def gradedPieceToCohomology (K : DerivedCategory A) (j : ℤ) :
    (DerivedCategory.truncationFilteredPreimage K).gradedPiece (-j) ⟶
      (CochainComplex.singleFunctor A j).obj
        ((DerivedCategory.homologyFunctor A j).obj K) :=
  (CochainComplex.TruncationFiltration.Step.gradedPieceIsoCokernel
      (DerivedCategory.Q.objPreimage K) j).hom ≫
    truncationStepToCohomology (DerivedCategory.Q.objPreimage K) j ≫
    (CochainComplex.singleFunctor A j).map
      (DerivedCategory.ShiftedHom.Boundary.representativeHomologyIso K j).inv

/-- Precomposing the graded-piece comparison with the stage quotient gives the canonical
cycles-to-homology projection of the upper truncation. -/
@[stacks 0BKM "quotient specification of the truncation graded-piece comparison"]
theorem π_gradedPieceToCohomology (K : DerivedCategory A) (j : ℤ) :
    cokernel.π ((DerivedCategory.truncationFilteredPreimage K).stageComparison
        (lt_add_one (-j)).le) ≫
      (HomologicalComplex.Filtered.TwoStep.GradedPiece.cokernelIso
        (DerivedCategory.truncationFilteredPreimage K) (-j)).inv ≫
      gradedPieceToCohomology K j =
    (CochainComplex.TruncationFiltration.Step.iso (DerivedCategory.Q.objPreimage K) j).hom ≫
      DerivedCategory.ShiftedHom.Boundary.cochainProjection
        (DerivedCategory.Q.objPreimage K) j ≫
      (CochainComplex.singleFunctor A j).map
        (DerivedCategory.ShiftedHom.Boundary.representativeHomologyIso K j).inv := by
  dsimp only [gradedPieceToCohomology]
  dsimp only [DerivedCategory.truncationFilteredPreimage]
  have h := congrArg
    (fun f ↦ f ≫ truncationStepToCohomology (DerivedCategory.Q.objPreimage K) j ≫
      (CochainComplex.singleFunctor A j).map
        (DerivedCategory.ShiftedHom.Boundary.representativeHomologyIso K j).inv)
    (CochainComplex.TruncationFiltration.Step.π_gradedPieceIsoCokernel_hom
      (DerivedCategory.Q.objPreimage K) j)
  simpa only [Category.assoc, π_truncationStepToCohomology_assoc] using h

/-- The canonical comparison is a quasi-isomorphism for every derived object, without a
boundedness or formality assumption. -/
@[stacks 0BKM "quasi-isomorphism of the truncation graded-piece comparison"]
theorem gradedPieceToCohomology_quasiIso (K : DerivedCategory A) (j : ℤ) :
    QuasiIso (gradedPieceToCohomology K j) := sorry

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- The standard page-and-bidegree renumbering of a realization of the truncation filtration. -/
@[stacks 0BKM "renumbered sequence of a truncation-filtration realization"]
noncomputable abbrev renumberedSequence {K : DerivedCategory A}
    (S : RightDerived.SpectralSequence.Realization F
      (DerivedCategory.truncationFilteredPreimage K)) :
    E₂CohomologicalSpectralSequence B :=
  CohomologicalSpectralSequence.Renumber.fromZero S.sequence

/-- A truncation-filtration realization of the hypercohomology spectral sequence.  It retains the
original associated sequence, uses the standard deterministic renumbering, and records the
second-page and abutment comparisons with the total right-derived functor. -/
@[stacks 0BKM "truncation-filtration right-derived spectral sequence"]
structure Realization (K : DerivedCategory A) where
  /-- The right-derived realization of the canonical truncation filtration. -/
  original : RightDerived.SpectralSequence.Realization F
    (DerivedCategory.truncationFilteredPreimage K)
  /-- The second page of the renumbered sequence is `R^i F (H^j K)`. -/
  pageTwoIso : ∀ (i : ℕ) (j : ℤ),
    ((renumberedSequence F original).page 2).X (Int.ofNat i, j) ≅
      (F.rightDerived i).obj ((DerivedCategory.homologyFunctor A j).obj K)
  /-- The filtered model abuts to the cohomology of the total right-derived value at `K`. -/
  targetIso : ∀ n : ℤ,
    original.filtered.underlying.homology n ≅
      (Functor.RightDerived.Homotopy.cohomologyFunctor F n).obj K

namespace Realization

/-- The canonical cochain map from the `(-j)`-th graded piece to the degree-`j` cohomology
object placed in degree `j`, independent of the realization. -/
noncomputable abbrev gradedPieceMap {K : DerivedCategory A} (_S : Realization F K) (j : ℤ) :
    (DerivedCategory.truncationFilteredPreimage K).gradedPiece (-j) ⟶
      (CochainComplex.singleFunctor A j).obj
        ((DerivedCategory.homologyFunctor A j).obj K) :=
  gradedPieceToCohomology K j

/-- The canonical graded-piece map of a realization is a quasi-isomorphism. -/
theorem gradedPieceMap_quasiIso {K : DerivedCategory A} (S : Realization F K) (j : ℤ) :
    QuasiIso (gradedPieceMap (F := F) S j) :=
  gradedPieceToCohomology_quasiIso K j

/-- The graded-piece comparison becomes invertible after derived localization.
This is an invertibility certificate, not an isomorphism of cochain complexes. -/
theorem gradedPieceIso {K : DerivedCategory A} (S : Realization F K) (j : ℤ) :
    IsIso (DerivedCategory.Q.map (gradedPieceMap (F := F) S j)) := by
  letI := gradedPieceMap_quasiIso (F := F) S j
  infer_instance

/-- The filtered model retained before the standard renumbering. -/
@[stacks 0BKM "filtered model of a truncation-filtration realization"]
noncomputable abbrev filtered {K : DerivedCategory A} (S : Realization F K) :
    FilteredComplex B :=
  S.original.filtered

/-- The associated sequence retained before the standard renumbering. -/
@[stacks 0BKM "original sequence of a truncation-filtration realization"]
noncomputable abbrev originalSequence {K : DerivedCategory A} (S : Realization F K) :
    CohomologicalSpectralSequence B 0 :=
  S.original.sequence

/-- The displayed `E₂` spectral sequence obtained by the standard renumbering. -/
@[stacks 0BKM "renumbered sequence of a truncation-filtration realization"]
noncomputable abbrev sequence {K : DerivedCategory A} (S : Realization F K) :
    E₂CohomologicalSpectralSequence B :=
  renumberedSequence F S.original

/-- The original sequence is associated to the filtered right-derived model. -/
@[stacks 0BKM "association of a truncation-filtration realization"]
theorem isAssociated {K : DerivedCategory A} (S : Realization F K) :
    FilteredComplex.IsAssociated S.filtered S.originalSequence := sorry

/-- The displayed sequence is the standard page-and-bidegree renumbering of the original
associated sequence. -/
@[stacks 0BKM "renumbering of a truncation-filtration realization"]
theorem isRenumbering {K : DerivedCategory A} (S : Realization F K) :
    CohomologicalSpectralSequence.Renumber.IsFromZero
      S.originalSequence S.sequence := sorry

/-- Every derived object admits a truncation-filtration right-derived realization. -/
@[stacks 0BKM]
theorem nonempty [IsGrothendieckAbelian.{w} A] (K : DerivedCategory A) :
    Nonempty (Realization F K) := sorry

/-- A bounded-below derived object gives a bounded renumbered spectral sequence. -/
@[stacks 0BKM "boundedness of a truncation-filtration realization"]
theorem isBounded {K : DerivedCategory A} (S : Realization F K)
    (hK : DerivedCategory.IsBoundedBelow K) : S.sequence.IsBounded := sorry

/-- A bounded-below derived object gives finite filtrations on the abutment cohomology. -/
@[stacks 0BKM "finite filtration of a truncation-filtration realization"]
theorem finite {K : DerivedCategory A} (S : Realization F K)
    (hK : DerivedCategory.IsBoundedBelow K) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- A bounded-below derived object gives convergence of the original sequence together with its
standard renumbering. -/
@[stacks 0BKM "convergence of a truncation-filtration realization"]
theorem converges {K : DerivedCategory A} (S : Realization F K)
    (hK : DerivedCategory.IsBoundedBelow K) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering
      S.filtered S.originalSequence S.sequence := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
