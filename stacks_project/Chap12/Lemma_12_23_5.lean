/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.SpectralSequence
import StacksCheckRecall

/-!
# Lemma 12.23.5

Source-facing checks for the limit page of a spectral sequence associated to a filtered
differential object.  The shared owner uses all-page `Zᵣ/Bᵣ` presentations; a comparison of only
the zeroth or first page does not determine the limit page.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
variable (hAssoc : HomologicalComplex.Filtered.Page.HasPresentation K E)
variable
  (L : SpectralSequence.LimitStages
    (HomologicalComplex.Filtered.Page.One.tail E))

/- Lemma 12.23.5 (1) [012F]: explicit eventual boundary and cycle stages produce the graded
limit object whose degree-`p` term is `Z∞^p / B∞^p`. -/
@[stacks 012F]
#check (L.infinityPageObject : GradedObject ℤ C)

/- Lemma 12.23.5 (2) [012F]: the associated graded of the induced homology filtration is
degreewise a subquotient of the graded limit object. -/
@[stacks 012F]
#check (HomologicalComplex.Filtered.LimitPage.graded_isSubquotient
  K E hAssoc L :
    ∀ p : ℤ,
      IsSubquotient
        ((HomologicalComplex.Filtered.Homology.Filtration.induced K PUnit.unit).gradedPiece p)
        (L.infinityPageObject p))
