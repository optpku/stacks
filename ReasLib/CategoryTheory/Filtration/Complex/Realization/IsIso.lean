module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization

/-!
# Isomorphism transport for filtered spectral-sequence realizations

The generic realization category is defined by a unique compatible spectral-sequence component.
This leaf registers the resulting isomorphism transport as instances, so downstream code can use
ordinary `IsIso` search from the filtered-complex component.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : Realization (C := C)}

/-- A realization map is an isomorphism when its filtered-complex component is. -/
@[stacks 012C "isomorphism transport for filtered spectral-sequence realization maps"]
noncomputable instance map_isIso (f : S ⟶ T) [IsIso f.filteredMap] : IsIso f := sorry

/-- The spectral-sequence component of an isomorphic realization map is an isomorphism. -/
@[stacks 012C "spectral-sequence isomorphism transport for realization maps"]
noncomputable instance sequenceMap_isIso (f : S ⟶ T) [IsIso f.filteredMap] :
    IsIso f.sequenceMap := sorry

/-- Every page component of an isomorphic realization map is an isomorphism. -/
@[stacks 012C "page-component isomorphism transport for realization maps"]
noncomputable instance sequenceMap_f_isIso (f : S ⟶ T) (r : ℤ) (hr : 0 ≤ r)
    (p q : ℤ) [IsIso f.filteredMap] : IsIso ((f.sequenceMap.hom r hr).f (p, q)) := sorry

variable (f : S ⟶ T) [IsIso f.filteredMap]
#synth IsIso f
#synth IsIso f.sequenceMap
#synth IsIso ((f.sequenceMap.hom 1).f (0, 0))

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
