module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Functor

/-!
# Isomorphism transport for spectral-sequence renumbering

The renumbering functor preserves categorical isomorphisms.  The named instances below expose
both the bundled map and each renumbered page map, which keeps clients from unfolding the affine
bidegree restriction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E E' : CohomologicalSpectralSequence C 1}

/-- Renumbering sends an isomorphism of spectral sequences to an isomorphism. -/
@[stacks 0G1Y "isomorphism transport under spectral-sequence renumbering"]
noncomputable instance map_isIso (f : E ⟶ E') [IsIso f] :
    IsIso (map f) := sorry

/-- Every page map of a renumbered isomorphism is an isomorphism. -/
@[stacks 0G1Y "isomorphism on renumbered pages"]
noncomputable instance map_hom_isIso (f : E ⟶ E') (r : ℤ) (hr : 2 ≤ r) [IsIso f] :
    IsIso ((map f).hom r hr) := sorry

end CategoryTheory.CohomologicalSpectralSequence.Renumber
