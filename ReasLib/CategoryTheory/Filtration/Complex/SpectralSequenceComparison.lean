/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Comparison of Spectral Sequences of Filtered Complexes

This leaf records the reusable page-one comparison criterion. It is independent of any
particular source of the filtered complexes, such as injective resolutions or derived functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Association.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A map of filtered complexes which is an isomorphism on the cohomology of every graded piece
is an isomorphism from page one onward on every association-induced spectral-sequence map. -/
@[stacks 015W "canonical page-one comparison criterion"]
theorem isIsoFrom {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {f : K ⟶ L}
    (φ : Association.Hom A B f)
    (hpage : ∀ p q : ℤ,
      IsIso (HomologicalComplex.homologyMap (gradedPieceMap f p) (p + q))) :
    φ.hom.IsIsoFrom 1 zero_le_one := sorry

/-- Source-facing existential form of the page-one comparison criterion. -/
@[stacks 015W "page-one comparison criterion"]
theorem existsIso {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (f : K ⟶ L)
    (hpage : ∀ p q : ℤ,
      IsIso (HomologicalComplex.homologyMap (gradedPieceMap f p) (p + q))) :
    ∃ e : Association.Hom A B f, e.hom.IsIsoFrom 1 zero_le_one := sorry

end CategoryTheory.FilteredComplex.Association.Hom
