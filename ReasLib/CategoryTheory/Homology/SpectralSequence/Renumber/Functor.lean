module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Functoriality of spectral-sequence renumbering

The canonical page-and-bidegree renumbering is a construction on spectral sequences, not merely
on their underlying pages.  This file owns its morphism, functor, and comparison API.  Keeping the
map layer separate from the object definition makes the latter useful in lightweight imports while
giving downstream constructions a canonical naturality entry point.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence
namespace Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Restrict every page map of `f` along the standard renumbering bidegree embedding. -/
@[stacks 0G1Y, stacks 0G20]
noncomputable def map {E E' : CohomologicalSpectralSequence C 1} (f : E ⟶ E') :
    renumber E ⟶ renumber E' where
  hom r hr :=
    HomologicalComplex.restrictionMap
      (f.hom (r - 1) (one_le_priorPage r hr)) (pageEmbedding r)
  comm r r' pq hrr' hr := sorry

/-- Renumbering sends an identity morphism to the identity morphism. -/
@[simp, stacks 0G1Y, stacks 0G20]
theorem map_id (E : CohomologicalSpectralSequence C 1) :
    map (𝟙 E) = 𝟙 (renumber E) := sorry

/-- Renumbering preserves composition of spectral-sequence morphisms. -/
@[simp, stacks 0G1Y, stacks 0G20]
theorem map_comp {E E' E'' : CohomologicalSpectralSequence C 1}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The canonical renumbering is functorial in a cohomological spectral sequence beginning at `E₁`. -/
@[stacks 0G1Y, stacks 0G20]
noncomputable def functor :
    CohomologicalSpectralSequence C 1 ⥤ E₂CohomologicalSpectralSequence C where
  obj E := renumber E
  map f := map f
  map_id E := map_id E
  map_comp f g := map_comp f g

namespace Functor

/-- Evaluation of the renumbering functor on an object. -/
@[simp, stacks 0G1Y, stacks 0G20]
theorem obj (E : CohomologicalSpectralSequence C 1) :
    (Renumber.functor (C := C)).obj E = renumber E := rfl

/-- Evaluation of the renumbering functor on a morphism. -/
@[simp, stacks 0G1Y, stacks 0G20]
theorem map {E E' : CohomologicalSpectralSequence C 1} (f : E ⟶ E') :
    (Renumber.functor (C := C)).map f = Renumber.map f := rfl

end Functor

/-- An isomorphism from page `r` onward remains an isomorphism after renumbering the pages.

The lower-bound hypothesis is explicit because the source starts at `E₁`, whereas the target
renumbered sequence starts at `E₂`. -/
@[stacks 0G1Y, stacks 0G20]
theorem isIsoFrom {E E' : CohomologicalSpectralSequence C 1} {f : E ⟶ E'}
    {r : ℤ} (hr : 1 ≤ r)
    (h : SpectralSequence.Hom.IsIsoFrom f r hr) :
    SpectralSequence.Hom.IsIsoFrom (map f) (r + 1) (two_le_pageSucc hr) := sorry

end Renumber
end CohomologicalSpectralSequence
end CategoryTheory
