module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Views of unbounded filtered right-derived realizations

This file exposes the filtered model, spectral sequence, association, first page, and abutment of a realization.
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

namespace SpectralSequence

namespace Realization

/-- The filtered model underlying a right-derived spectral-sequence realization. -/
@[stacks 0BKK "filtered model of a right-derived realization"]
noncomputable abbrev filtered {K : FilteredComplex A} (S : Realization F K) :
    FilteredComplex B :=
  model F S.resolution

/-- The associated cohomological spectral sequence of a right-derived realization. -/
@[stacks 0BKK "spectral sequence of a filtered right-derived realization"]
noncomputable abbrev sequence {K : FilteredComplex A} (S : Realization F K) :
    CohomologicalSpectralSequence B 0 :=
  S.associated.sequence

/-- The concrete association of a right-derived realization with its filtered model. -/
@[stacks 0BKK "association of a filtered right-derived realization"]
noncomputable abbrev association {K : FilteredComplex A} (S : Realization F K) :
    FilteredComplex.Association S.filtered S.sequence :=
  S.associated.association

/-- The first page of a realization is total right-derived cohomology of the graded pieces. -/
@[stacks 0BKK "first page of an unbounded filtered right-derived spectral sequence"]
noncomputable abbrev pageOneIso {G : A ⥤ B} [G.Additive] [G.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived G]
    {K : FilteredComplex A} (S : Realization G K) (p q : ℤ) :
    (S.sequence.page 1).X (p, q) ≅ cochainCohomology G (K.gradedPiece p) (p + q) :=
  S.association.pageOneIso p q ≪≫ S.comparison.gradedPieceIso p (p + q)

/-- The forward first-page comparison is the association comparison followed by the model
graded-piece comparison. -/
@[simp, stacks 0BKK "forward first-page comparison for a right-derived realization"]
theorem pageOneIso_hom {G : A ⥤ B} [G.Additive] [G.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived G]
    {K : FilteredComplex A} (S : Realization G K) (p q : ℤ) :
    (S.pageOneIso p q).hom =
      (S.association.pageOneIso p q).hom ≫
        (S.comparison.gradedPieceIso p (p + q)).hom := sorry

/-- The inverse first-page comparison first returns through the model graded-piece comparison and
then through the association comparison. -/
@[simp, stacks 0BKK "inverse first-page comparison for a right-derived realization"]
theorem pageOneIso_inv {G : A ⥤ B} [G.Additive] [G.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived G]
    {K : FilteredComplex A} (S : Realization G K) (p q : ℤ) :
    (S.pageOneIso p q).inv =
      (S.comparison.gradedPieceIso p (p + q)).inv ≫
        (S.association.pageOneIso p q).inv := sorry

/-- The cohomology of the filtered model is total right-derived cohomology of the underlying
complex. -/
@[stacks 0BKK "abutment of an unbounded filtered right-derived spectral sequence"]
noncomputable abbrev targetIso {G : A ⥤ B} [G.Additive] [G.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived G]
    {K : FilteredComplex A} (S : Realization G K) (n : ℤ) :
    S.filtered.underlying.homology n ≅ cochainCohomology G K.underlying n :=
  S.comparison.underlyingIso n

/-- A right-derived realization supplies the canonical existential association predicate. -/
@[stacks 0BKK "association of a right-derived spectral sequence"]
theorem isAssociated {K : FilteredComplex A} (S : Realization F K) :
    FilteredComplex.IsAssociated S.filtered S.sequence := sorry

end Realization

end SpectralSequence

end CategoryTheory.FilteredComplex.RightDerived
