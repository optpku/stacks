module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Isomorphism transport for fixed first-page rows

An isomorphism of spectral sequences induces an isomorphism on every fixed row of the first page.
Both component and bundled instances are exposed independently of the row computations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.PageOneRow

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E E' : CohomologicalSpectralSequence C 0}

/-- Every component of a fixed first-page row map is an isomorphism when its source map is. -/
@[stacks 0130 "isomorphism on fixed first-page row components"]
noncomputable instance map_f_isIso (f : E ⟶ E') (q p : ℤ) [IsIso f] :
    IsIso ((map f q).f p) := sorry

/-- A fixed first-page row map is an isomorphism when its spectral-sequence map is. -/
@[stacks 0130 "isomorphism of fixed first-page row maps"]
noncomputable instance map_isIso (f : E ⟶ E') (q : ℤ) [IsIso f] :
    IsIso (map f q) := sorry

/-- Every component of a fixed first-page row map is an isomorphism when the spectral-sequence map
is an isomorphism from the first page onward. -/
@[stacks 0130 "row components from a pagewise spectral-sequence comparison"]
theorem map_f_isIso_of_isIsoFrom (f : E ⟶ E') (q p : ℤ)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 zero_le_one) :
    IsIso ((map f q).f p) := sorry

/-- A fixed first-page row map is an isomorphism when the spectral-sequence map is an isomorphism
from the first page onward. -/
@[stacks 0130 "row map from a pagewise spectral-sequence comparison"]
theorem map_isIso_of_isIsoFrom (f : E ⟶ E') (q : ℤ)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 zero_le_one) :
    IsIso (map f q) := sorry

variable (f : E ⟶ E') [IsIso f]
#synth IsIso ((map f 0).f 0)
#synth IsIso (map f 0)

end CategoryTheory.CohomologicalSpectralSequence.PageOneRow
