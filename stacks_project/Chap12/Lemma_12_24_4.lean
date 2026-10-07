module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
import StacksCheckRecall

/-!
# Functoriality of the Associated Spectral Sequence

The reusable owner states unique existence of the spectral-sequence morphism induced by a
filtered-complex morphism. It records both the map on associated graded complexes at `E₀` and the
map induced on every explicit `Zᵣ/Bᵣ` page representative.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : FilteredComplex C}
variable {E E' : CohomologicalSpectralSequence C 0}
variable (A : FilteredComplex.Association K E) (B : FilteredComplex.Association L E')
variable (α : K ⟶ L)

/- Lemma 12.24.4 (012O): a morphism of filtered complexes induces a unique morphism between the
associated spectral sequences, compatible with their bigradings. -/
@[stacks 012O "canonical morphism of associated spectral sequences"]
#check (FilteredComplex.Association.Map.existsUnique A B α :
  ∃! φ : E ⟶ E', FilteredComplex.Association.Map.IsInduced A B α φ)

#check FilteredComplex.Association.Map.IsInduced

#check FilteredComplex.Association.Map.pageOneIso_hom_naturality
