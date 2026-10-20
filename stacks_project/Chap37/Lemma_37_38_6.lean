/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.EtaleNeighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/- Lemma 37.38.6: a smooth morphism admits a lift over an étale neighbourhood of
every point in its image. -/
@[stacks 055U] #check
  (AlgebraicGeometry.Smooth.exists_etaleNeighborhood_lift :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
      (s : S) (hs : s ∈ Set.range f),
      ∃ (U : Scheme.EtaleNeighborhood S s) (g : U.toEtale.left ⟶ X),
        g ≫ f = U.toEtale.hom)

end AlgebraicGeometry.Smooth
