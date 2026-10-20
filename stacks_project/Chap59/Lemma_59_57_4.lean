/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RepresentationTheory.Homological.ContCohomology.DiscreteModule
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Action
open CategoryTheory.Action.ModuleCat

@[expose] public section

universe u

/- Lemma 59.57.4 -/
@[stacks 0DVE] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.ext_groupCohomology_iso_of_finiteProjective :
    ∀ {R G : Type u} [CommRing R] [Group G]
      [TopologicalSpace G] [IsTopologicalGroup G]
      (M N : DiscreteModuleCat R G) (i : ℕ)
      (hM : Module.FiniteProjective R M.obj.V),
      Nonempty
        (ModuleCat.of R (CategoryTheory.Abelian.Ext M N i) ≅
          DiscreteModuleCat.cohomologyObject R G i
            (DiscreteModuleCat.dualTensor M N hM)))

end
