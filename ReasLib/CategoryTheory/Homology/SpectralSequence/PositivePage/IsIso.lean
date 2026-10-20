module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.OfZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Isomorphism transport for positive pages

This leaf separates pagewise isomorphism transport from the positive-page definitions.  It gives
both the usual categorical `IsIso` instances and an explicit bridge from the stronger and more
useful `SpectralSequence.Hom.IsIsoFrom` comparison hypothesis.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

namespace Page.One

/-- Forgetting the zeroth page preserves isomorphisms of spectral sequences. -/
@[stacks 0BDU "isomorphism transport for the page-one view"]
noncomputable instance map_isIso
    {E E' : SpectralSequence C c 0} (f : E ⟶ E') [IsIso f] :
    IsIso (map f) := sorry

end Page.One

namespace PositivePageFunctor

/-- A positive-page complex map is an isomorphism when the spectral-sequence map is. -/
@[stacks 011O "isomorphism on positive-page complexes"]
noncomputable instance map_isIso
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (r : ℕ+) [IsIso f] :
    IsIso ((positivePageFunctor (C := C) c r).map f) := sorry

end PositivePageFunctor

namespace PageObjectFunctor

/-- A positive-page entry map is an isomorphism when the spectral-sequence map is. -/
@[stacks 011O "isomorphism on positive-page entries"]
noncomputable instance map_isIso
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (r : ℕ+) (pq : κ) [IsIso f] :
    IsIso ((pageObjectFunctor (C := C) c r pq).map f) := sorry

end PageObjectFunctor

namespace Hom

/-- Every entry on or after a specified positive page is an isomorphism under `IsIsoFrom`. -/
@[stacks 011O "positive-page entry isomorphism from a comparison"]
theorem isIsoFrom_entry
    {E E' : SpectralSequence C c 1} {f : E ⟶ E'}
    (h : IsIsoFrom f 1 le_rfl) (r : ℕ+) (pq : κ) :
    IsIso ((f.positivePage r).f pq) := sorry

/-- The bundled positive-page complex map is an isomorphism under `IsIsoFrom`. -/
@[stacks 011O "positive-page complex isomorphism from a comparison"]
theorem isIsoFrom_page
    {E E' : SpectralSequence C c 1} {f : E ⟶ E'}
    (h : IsIsoFrom f 1 le_rfl) (r : ℕ+) :
    IsIso (f.positivePage r) := sorry

variable {E E' : SpectralSequence C c 0} (f : E ⟶ E') [IsIso f]
#synth IsIso (Page.One.map f)

end Hom

end SpectralSequence
end CategoryTheory
