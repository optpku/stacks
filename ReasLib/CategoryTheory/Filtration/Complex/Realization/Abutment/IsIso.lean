module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.IsIso

/-!
# Isomorphism transport for realizations with abutments

An abutment comparison is proposition-valued extra structure on a generic realization map.  The
isomorphism status therefore comes from the inherited filtered-complex component and is exposed
here as a small downstream-facing support leaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization.WithAbutment.Map

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type u'} [Category.{v'} I]
variable {H : ℤ → (I ⥤ C)}
variable {X Y : I} {f : X ⟶ Y}
variable {S : WithAbutment H X} {T : WithAbutment H Y}

/-- The spectral-sequence component of an isomorphic abutment map is an isomorphism. -/
@[stacks 012C "spectral-sequence isomorphism transport for realization maps with abutment"]
noncomputable instance sequenceMap_isIso (m : Map H f S T) [IsIso m.filteredMap] :
    IsIso m.sequenceMap := sorry

/-- Every page component of an isomorphic abutment map is an isomorphism. -/
@[stacks 012C "page-component isomorphism transport for realization maps with abutment"]
noncomputable instance sequenceMap_f_isIso (m : Map H f S T) (r : ℤ) (hr : 0 ≤ r)
    (p q : ℤ) [IsIso m.filteredMap] : IsIso ((m.sequenceMap.hom r hr).f (p, q)) := sorry

variable (m : Map H f S T) [IsIso m.filteredMap]
#synth IsIso m.sequenceMap
#synth IsIso ((m.sequenceMap.hom 1).f (0, 0))

end CategoryTheory.FilteredComplex.SpectralSequence.Realization.WithAbutment.Map
