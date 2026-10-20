/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Spectral.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

/- Lemma 59.82.4: if `Z` is closed in a spectral space `X` and each intersection
`Z ∩ closure ({x} : Set X)` is connected, restriction identifies global sections of every sheaf
on `X` with global sections on `Z`. -/
@[stacks 09ZG] #check
  (TopCat.Sheaf.globalSectionsBijectiveOfConnectedClosureIntersections :
    ∀ {X : TopCat.{u}} [SpectralSpace X] {Z : Set X},
      IsClosed Z →
      (∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) →
      (F : X.Sheaf (Type u)) →
      Function.Bijective
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
          (TopCat.subsetInclusion Z)).unit.app F).hom.app (op (⊤ : Opens X))) )

end

end
