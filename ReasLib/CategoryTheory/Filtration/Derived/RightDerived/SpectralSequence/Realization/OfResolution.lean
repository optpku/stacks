module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unbounded right-derived realizations from explicit data

This leaf is the data-owner constructor for a realization.  A resolution, its cohomology
comparison, and an associated spectral sequence are all explicit inputs; no choice is hidden
behind the constructor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization

/-- Build an unbounded right-derived realization from an explicit resolution, comparison, and
associated spectral sequence. -/
@[stacks 0BKK "realization from explicit resolution data"]
noncomputable def ofResolution
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    Realization F K where
  resolution := R
  comparison := P
  associated := E

/-- The explicit resolution is retained by `Realization.ofResolution`. -/
@[simp, stacks 0BKK "resolution of an explicit right-derived realization"]
theorem ofResolution_resolution
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).resolution = R := sorry

/-- The supplied model comparison is retained by `Realization.ofResolution`. -/
@[simp, stacks 0BKK "comparison of an explicit right-derived realization"]
theorem ofResolution_comparison
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).comparison = P := sorry

/-- The supplied associated spectral sequence is retained by `Realization.ofResolution`. -/
@[simp, stacks 0BKK "association data of an explicit right-derived realization"]
theorem ofResolution_associated
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).associated = E := sorry

/-- The filtered model of an explicit realization is the model of its supplied resolution. -/
@[simp, stacks 0BKK "filtered model of an explicit right-derived realization"]
theorem ofResolution_filtered
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).filtered = model F R := sorry

/-- The spectral sequence of an explicit realization is the supplied sequence. -/
@[simp, stacks 0BKK "spectral sequence of an explicit right-derived realization"]
theorem ofResolution_sequence
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).sequence = E.sequence := sorry

/-- The association of an explicit realization is the supplied association. -/
@[simp, stacks 0BKK "association of an explicit right-derived realization"]
theorem ofResolution_association
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).association = E.association := sorry

/-- The first-page comparison of an explicit realization factors through the supplied association
and model comparison. -/
@[simp, stacks 0BKK "first page of an explicit right-derived realization"]
theorem ofResolution_pageOneIso
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) (p q : ℤ) :
    (ofResolution F R P E).pageOneIso p q =
      E.association.pageOneIso p q ≪≫ P.gradedPieceIso p (p + q) := sorry

/-- The abutment comparison of an explicit realization is the supplied underlying comparison. -/
@[simp, stacks 0BKK "abutment of an explicit right-derived realization"]
theorem ofResolution_targetIso
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) (n : ℤ) :
    (ofResolution F R P E).targetIso n = P.underlyingIso n := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
