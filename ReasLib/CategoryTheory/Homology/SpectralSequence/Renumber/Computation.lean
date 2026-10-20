/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for spectral-sequence renumbering

The functorial renumbering is defined by restriction along an affine bidegree equivalence.  This
small leaf records the component formula explicitly, so clients can use the displayed indices
without unfolding `HomologicalComplex.restrictionMap`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]

/- The page-map formula exposes the restriction construction without unfolding the functor. -/
/-- A renumbered page map is restriction of the preceding old page map. -/
@[simp, stacks 0G1Y "page-map computation for spectral-sequence renumbering", stacks 0G20]
theorem map_hom {E E' : CohomologicalSpectralSequence C 1} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) :
    (map f).hom r hr =
      HomologicalComplex.restrictionMap
        (f.hom (r - 1) (one_le_priorPage r hr)) (pageEmbedding r) := sorry

/- The component formula is the computation-facing counterpart of `map_id` and `map_comp`. -/
/-- The component of a renumbered page map is the old component at the affine bidegree. -/
@[simp, stacks 0G1Y "component computation for spectral-sequence renumbering", stacks 0G20]
theorem map_hom_f {E E' : CohomologicalSpectralSequence C 1} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) (ij : ℤ × ℤ) :
    ((map f).hom r hr).f ij =
      (f.hom (r - 1) (one_le_priorPage r hr)).f (bidegreeEquiv ij) := sorry

end CategoryTheory.CohomologicalSpectralSequence.Renumber
