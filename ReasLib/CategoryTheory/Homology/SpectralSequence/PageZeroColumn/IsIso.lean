module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Isomorphism transport for fixed zeroth-page columns

An isomorphism of spectral sequences induces an isomorphism on every fixed column of the zeroth
page.  Both component and bundled instances live here so clients can use typeclass transport
without unfolding restriction maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.PageZeroColumn

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E E' : CohomologicalSpectralSequence C 0}

/-- Every component of a fixed zeroth-page column map is an isomorphism when its source map is. -/
@[stacks 012M "isomorphism on fixed zeroth-page column components"]
noncomputable instance map_f_isIso (f : E ⟶ E') (p q : ℤ) [IsIso f] :
    IsIso ((map f p).f q) := sorry

/-- A fixed zeroth-page column map is an isomorphism when its spectral-sequence map is. -/
@[stacks 012M "isomorphism of fixed zeroth-page column maps"]
noncomputable instance map_isIso (f : E ⟶ E') (p : ℤ) [IsIso f] :
    IsIso (map f p) := sorry

/-- Every component of a fixed zeroth-page column map is an isomorphism when the spectral-sequence
map is an isomorphism from the first page onward. -/
@[stacks 012M "column components from a pagewise spectral-sequence comparison"]
theorem map_f_isIso_of_isIsoFrom (f : E ⟶ E') (p q : ℤ)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 zero_le_one) :
    IsIso ((map f p).f q) := sorry

/-- A fixed zeroth-page column map is an isomorphism when the spectral-sequence map is an
isomorphism from the first page onward. -/
@[stacks 012M "column map from a pagewise spectral-sequence comparison"]
theorem map_isIso_of_isIsoFrom (f : E ⟶ E') (p : ℤ)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 zero_le_one) :
    IsIso (map f p) := sorry

variable (f : E ⟶ E') [IsIso f]
#synth IsIso ((map f 0).f 0)
#synth IsIso (map f 0)

end CategoryTheory.CohomologicalSpectralSequence.PageZeroColumn
