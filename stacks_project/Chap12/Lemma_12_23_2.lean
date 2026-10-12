/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.SpectralSequence
import StacksCheckRecall

/-!
# Lemma 12.23.2

Source-facing checks for the spectral sequence of a filtered differential object.  Association
means an all-page `Zᵣ/Bᵣ` presentation together with the zeroth-page comparison; later pages are
not manufactured from zeroth-page data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/- Lemma 12.23.2 [012C]: every filtered differential object admits an associated spectral
sequence with the stated all-page representatives and initial-page comparison. -/
@[stacks 012C]
#check (HomologicalComplex.Filtered.Association.exists K :
  ∃ E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0,
    HomologicalComplex.Filtered.Association.IsAssociated K E)

/- The degree-`p` entry on page `r` is represented by the explicit quotient `Zᵣ^p/Bᵣ^p`. -/
#check HomologicalComplex.Filtered.Page.Presentation.pageIso

/- The association records that the zeroth page is the associated graded differential object. -/
#check HomologicalComplex.Filtered.Association.pageZeroIso

/- The first-page identification with `H(gr^p K)` is derived from the zeroth-page comparison. -/
#check HomologicalComplex.Filtered.Association.PageOne.iso
