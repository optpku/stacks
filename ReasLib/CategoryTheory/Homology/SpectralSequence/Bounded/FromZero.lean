module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Boundedness of zero-based spectral sequences

The boundedness predicate on a zero-based sequence is conventionally tested on its positive-page
view.  This owner keeps that convention explicit without making clients mention `Page.One.ofZero`
in every statement.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A zero-based cohomological spectral sequence is bounded when its positive-page view is bounded.
-/
@[stacks 0BDU "boundedness of a zero-based spectral sequence"]
def IsBoundedFromZero (E : CohomologicalSpectralSequence C 0) : Prop :=
  IsBounded (SpectralSequence.Page.One.ofZero E)

/-- The zero-based boundedness predicate unfolds to boundedness of the positive-page view. -/
@[simp, stacks 0BDU "characterization of zero-based boundedness"]
theorem isBoundedFromZero_iff (E : CohomologicalSpectralSequence C 0) :
    IsBoundedFromZero E ↔
      IsBounded (SpectralSequence.Page.One.ofZero E) := sorry

end CategoryTheory.CohomologicalSpectralSequence
