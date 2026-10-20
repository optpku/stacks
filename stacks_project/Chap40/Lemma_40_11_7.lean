/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.ReducedRelationClosure

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.11.7: if the object scheme is the spectrum of a field, then the reduced closure
of the image of `(t, s)` is set-theoretically closed under outer-pair composition. -/
@[stacks 04QB] #check
  (AlgebraicGeometry.GroupoidScheme.reducedRelationClosureComposition_range_subset :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      Set.range (reducedRelationClosureComposition G).left ⊆
        Set.range (Scheme.Hom.reducedImageClosureιOver G.toPreRelation.hom).left)

end AlgebraicGeometry.GroupoidScheme
