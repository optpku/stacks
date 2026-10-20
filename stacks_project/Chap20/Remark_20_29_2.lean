/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteReplacement
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered.Finite
import StacksCheckRecall

@[expose] public section

/- [stacks 0BKL] Remark 20.29.2: for a bounded-below complex with finite filtrations, one may
construct the hypercohomology spectral sequence directly by choosing a strict filtered-injective
replacement and applying the left-exact filtered spectral-sequence construction. -/

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Finite

#check @CategoryTheory.FilteredComplex.StrictReplacement.exists_of_finiteFiltrations
#check @CochainComplex.FilteredInjectivePlus.Resolution
#check @CochainComplex.FilteredInjectivePlus.Resolution.nonempty
#check @leftExactFunctor
#check @gradedPieceComplex
#check @underlyingComplex
#check @gradedPieceComplexMap
#check @underlyingComplexMap
#check @model
@[stacks 0BKL] #check @Realization.nonempty
#check @Realization
#check @Realization.pageOneIso
#check @Realization.targetIso
#check @Realization.Map
#check @Realization.Map.pageOne_hom
#check @Realization.Map.target_hom
#check @Realization.Map.id
#check @Realization.Map.comp
#check @Realization.Map.reindex
#check @Realization.Map.reindex_rfl
#check @Realization.Map.id_comp
#check @Realization.Map.comp_id
#check @Realization.Map.assoc
#check @Realization.existsMap
#check @Realization.isBounded
#check @Realization.finite
#check @Realization.converges
#check @Realization.existsIsoFromOne

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Finite
