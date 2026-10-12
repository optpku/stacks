/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism.IsIso

/-!
# Isomorphism transport for total associated spectral sequences

An isomorphism of filtered complexes canonically lifts through the chosen association.  This leaf
registers the resulting instances so applications can ask for `IsIso` at the total, spectral
sequence, or page-entry level without rebuilding the lift.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.AssociatedSpectralSequence.Total

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : Total (C := C)}

/-- A total associated-spectral-sequence map is an isomorphism when its filtered-complex component
is an isomorphism. -/
@[stacks 012O "isomorphism transport for total associated spectral-sequence maps"]
noncomputable instance map_isIso (f : S ⟶ T) [IsIso f.filteredMap] : IsIso f := sorry

/-- Isomorphism status can equivalently be supplied through the filtered-complex forgetful
functor. -/
@[stacks 012O "isomorphism reflection by the total filtered-complex forgetful functor"]
theorem isIso_of_forgetFiltered_map_isIso (f : S ⟶ T)
    [IsIso ((forgetFiltered (C := C)).map f)] : IsIso f := sorry

/-- The spectral-sequence component of an isomorphic total map is an isomorphism. -/
@[stacks 012O "spectral-sequence isomorphism transport for total maps"]
noncomputable instance sequenceMap_isIso (f : S ⟶ T) [IsIso f.filteredMap] :
    IsIso (Hom.sequenceMap f) := sorry

/-- Every page component of an isomorphic total map is an isomorphism. -/
@[stacks 012O "page-component isomorphism transport for total maps"]
noncomputable instance sequenceMap_f_isIso (f : S ⟶ T) (r : ℤ) (hr : 0 ≤ r)
    (p q : ℤ) [IsIso f.filteredMap] :
    IsIso (((Hom.sequenceMap f).hom r hr).f (p, q)) := sorry

variable (f : S ⟶ T) [IsIso f.filteredMap]
#synth IsIso f
#synth IsIso (Hom.sequenceMap f)
#synth IsIso (((Hom.sequenceMap f).hom 1).f (0, 0))

end CategoryTheory.FilteredComplex.AssociatedSpectralSequence.Total
