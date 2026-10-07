module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.OfZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Renumbering cohomological spectral sequences from page zero

The standard hypercohomology indexing first forgets `E₀` and then applies the affine
page-and-bidegree renumbering.  This file packages that recurring composite as an object map,
morphism map, and functor, with direct computation laws.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Forget the zeroth page and apply the standard page-and-bidegree renumbering. -/
@[stacks 0G1Y "renumbering a zero-based cohomological spectral sequence", stacks 0G20]
noncomputable abbrev fromZero (E : CohomologicalSpectralSequence C 0) :
    E₂CohomologicalSpectralSequence C :=
  renumber (SpectralSequence.Page.One.ofZero E)

namespace FromZero

/-- A page of the standard renumbering from page zero is the affine restriction of the preceding
page of the original sequence. -/
@[simp, stacks 0G1Y "page computation after renumbering from page zero", stacks 0G20]
theorem page (E : CohomologicalSpectralSequence C 0)
    (r : ℤ) (hr : 2 ≤ r) :
    (fromZero E).page r hr =
      Renumber.page (SpectralSequence.Page.One.ofZero E) r hr := sorry

/-- The map induced between the standard renumberings of zero-based spectral sequences. -/
@[stacks 0G1Y "map of renumbered zero-based spectral sequences", stacks 0G20]
noncomputable abbrev map
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') :
    fromZero E ⟶ fromZero E' :=
  Renumber.map (SpectralSequence.Page.One.map f)

/-- A page map after standard renumbering from page zero is the restriction of the original
preceding page map. -/
@[simp, stacks 0G1Y "page-map computation after renumbering from page zero", stacks 0G20]
theorem map_hom
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) :
    (map f).hom r hr =
      HomologicalComplex.restrictionMap
        (f.hom (r - 1) (zero_le_one.trans (one_le_priorPage r hr)))
        (pageEmbedding r) := sorry

/-- A map between renumbered zero-based sequences is the original component at the affine
bidegree on the preceding page. -/
@[simp, stacks 0G1Y "component computation after renumbering from page zero", stacks 0G20]
theorem map_hom_f
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) (ij : ℤ × ℤ) :
    ((map f).hom r hr).f ij =
      (f.hom (r - 1) (zero_le_one.trans (one_le_priorPage r hr))).f
        (bidegreeEquiv ij) := sorry

/-- Renumbering from page zero preserves identity maps. -/
@[simp, stacks 0G1Y "identity law for renumbering from page zero", stacks 0G20]
theorem map_id (E : CohomologicalSpectralSequence C 0) :
    map (𝟙 E) = 𝟙 (fromZero E) := sorry

/-- Renumbering from page zero preserves composition of maps. -/
@[simp, stacks 0G1Y "composition law for renumbering from page zero", stacks 0G20]
theorem map_comp
    {E E' E'' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Forgetting `E₀` and applying the standard renumbering is functorial. -/
@[stacks 0G1Y "renumbering functor from page zero", stacks 0G20]
noncomputable def functor :
    CohomologicalSpectralSequence C 0 ⥤ E₂CohomologicalSpectralSequence C :=
  SpectralSequence.Page.One.functor
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) ⋙
    Renumber.functor

namespace Functor

/-- The composite renumbering functor acts on objects by `fromZero`. -/
@[simp, stacks 0G1Y "object computation for renumbering from page zero", stacks 0G20]
theorem obj (E : CohomologicalSpectralSequence C 0) :
    (FromZero.functor (C := C)).obj E = fromZero E := sorry

/-- The composite renumbering functor acts on morphisms by `FromZero.map`. -/
@[simp, stacks 0G1Y "map computation for renumbering from page zero", stacks 0G20]
theorem map {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') :
    (FromZero.functor (C := C)).map f = FromZero.map f := sorry

end Functor

end FromZero

end CategoryTheory.CohomologicalSpectralSequence.Renumber
