/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association

/-!
# Morphisms Compatible on the Zeroth Page

This file defines compatibility of a spectral-sequence morphism with a filtered-complex morphism
through chosen zeroth-page comparisons and derives the corresponding first-page naturality API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- A zeroth-page comparison commutes with the differentials in each fixed column. -/
theorem Page.Zero.Comparison.iso_commSq
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (p q : ℤ) :
    CommSq
      ((E.pageZeroColumn p).d q (q + 1))
      ((A.columnIso p).hom.f q)
      ((A.columnIso p).hom.f (q + 1))
      ((GradedPiece.Column.complex K p).d q (q + 1)) := sorry

/-- A morphism of spectral sequences is compatible at page zero with a morphism of filtered
complexes when every fixed-filtration column commutes with the canonical graded-piece
comparisons. -/
def Page.Zero.IsCompatible {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E')
    (α : K ⟶ L) (φ : E ⟶ E') : Prop :=
  ∀ p : ℤ,
    CommSq
      ((CohomologicalSpectralSequence.PageZeroColumn.functor p).map φ)
      ((A.columnIso p).hom)
      ((B.columnIso p).hom)
      ((GradedPiece.Column.functor p).map α)

/-- A map compatible with zeroth-page comparisons induces the expected natural square between
the corresponding first-page and graded-piece-homology comparisons. -/
@[reassoc, stacks 012M "naturality of the first-page comparison"]
theorem Page.One.iso_hom_naturality {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E')
    (α : K ⟶ L) (φ : E ⟶ E')
    (hφ : Page.Zero.IsCompatible A B α φ) (p q : ℤ) :
    (φ.hom 1).f (p, q) ≫ (Page.One.iso B p q).hom =
      (Page.One.iso A p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) := sorry

/-- Inverting the target first-page comparison recovers the first-page component from the
graded-piece homology map. -/
@[reassoc, stacks 012M "inverse naturality of the first-page comparison"]
theorem Page.One.iso_inv_naturality {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E')
    (α : K ⟶ L) (φ : E ⟶ E')
    (hφ : Page.Zero.IsCompatible A B α φ) (p q : ℤ) :
    HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (Page.One.iso B p q).inv =
      (Page.One.iso A p q).inv ≫ (φ.hom 1).f (p, q) := sorry

/-- Conjugating the graded-piece homology map by the first-page comparisons recovers the page
component of the spectral-sequence morphism. -/
@[reassoc, stacks 012M "computation of the first-page comparison"]
theorem Page.One.iso_naturality_inv {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E')
    (α : K ⟶ L) (φ : E ⟶ E')
    (hφ : Page.Zero.IsCompatible A B α φ) (p q : ℤ) :
    (Page.One.iso A p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (Page.One.iso B p q).inv =
      (φ.hom 1).f (p, q) := sorry

namespace Page.Zero.IsCompatible

variable {K L : FilteredComplex C} {E E' : CohomologicalSpectralSequence C 0}

/-- Identity morphisms are compatible with the same zeroth-page comparison. -/
theorem id (A : Page.Zero.Comparison K E) :
    Page.Zero.IsCompatible A A (𝟙 K) (𝟙 E) := sorry

/-- Page-zero compatibility is preserved by composition. -/
theorem comp {M : FilteredComplex C} {E'' : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E')
    (D : Page.Zero.Comparison M E'')
    {α : K ⟶ L} {β : L ⟶ M} {φ : E ⟶ E'} {ψ : E' ⟶ E''}
    (hφ : Page.Zero.IsCompatible A B α φ)
    (hψ : Page.Zero.IsCompatible B D β ψ) :
    Page.Zero.IsCompatible A D (α ≫ β) (φ ≫ ψ) := sorry

/-- Page-zero-compatible spectral-sequence morphisms have the same morphism on the zeroth page. -/
theorem hom_zero_eq (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E') (α : K ⟶ L)
    {φ ψ : E ⟶ E'}
    (hφ : Page.Zero.IsCompatible A B α φ)
    (hψ : Page.Zero.IsCompatible A B α ψ) :
    φ.hom 0 = ψ.hom 0 := sorry

/-- A morphism of spectral sequences is determined by its compatibility with a fixed filtered
complex morphism on the zeroth page. -/
theorem hom_ext (A : Page.Zero.Comparison K E) (B : Page.Zero.Comparison L E') (α : K ⟶ L)
    {φ ψ : E ⟶ E'}
    (hφ : Page.Zero.IsCompatible A B α φ)
    (hψ : Page.Zero.IsCompatible A B α ψ) :
    φ = ψ := sorry

end Page.Zero.IsCompatible

end FilteredComplex

end CategoryTheory
